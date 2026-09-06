"""Synthetic text surface forms. Metadata is never included in model features."""
import re
import numpy as np

NAMES={
 'teach':[['Aster','Bramble','Clover','Dahlia','Elm','Fern','Gorse','Hazel'],['Ari','Bea','Cal','Dee','Eli','Fay','Gus','Hal']],
 'selection':[['Iris','Juniper','Kalmia','Larch','Mallow','Nettle','Orchid','Poppy'],['Ivo','Jae','Kit','Lou','Moe','Nia','Ori','Paz']],
 'test':[['Quince','Rowan','Sorrel','Thistle','Umbel','Vetch','Willow','Yarrow'],['Quin','Rei','Sol','Tess','Uma','Val','Wes','Zed']]}
CUES={
 'teach':[[['soft leaves','rigid leaves'],['wet soil','dry soil']],
          [['a close friend','a stranger'],['a formal ceremony','an informal picnic']]],
 'selection':[[['delicate foliage','tough foliage'],['damp potting mix','arid potting mix']],
              [['someone familiar','someone unknown'],['an official reception','a relaxed gathering']]],
 'test':[[['pliable fronds','stiff fronds'],['waterlogged earth','parched earth']],
         [['an old companion','an unfamiliar visitor'],['a solemn state event','a casual get-together']]]}
TEMPLATES={
 'teach':[['Plant care for {name}: it has {a} and {b}. Choose a care class:',
           'The plant named {name} has {a}; its container has {b}. Care class:'],
          ['Letter for {name}: the recipient is {a} attending {b}. Choose a letter class:',
           'Write to {name}, who is {a}, about {b}. Letter class:']],
 'selection':[['A care decision is needed for {name}. Description: {a}; roots in {b}. Classification:',
               'Consider specimen {name}, showing {a} above {b}. Assign its care category:'],
              ['Correspondence to {name} concerns {b}; this person is {a}. Style classification:',
               'Select a writing category for {name}, {a}, at {b}:']],
 'test':[['How should specimen {name} be treated? Its signs are {a} and {b}. Care category:',
          'Regarding {name}: beneath {a} there is {b}. Decide its treatment category:'],
         ['A note will reach {name} during {b}. The addressee is {a}. Writing category:',
          'At {b}, {name} needs a message; the recipient is {a}. Choose its style category:']]}

def make_records():
    out=[]
    for pool in ['teach','selection','test']:
        for skill in [0,1]:
            for a in [0,1]:
                for b in [0,1]:
                    for name in NAMES[pool][skill]:
                        for tid,template in enumerate(TEMPLATES[pool][skill]):
                            text=template.format(name=name,a=CUES[pool][skill][0][a],b=CUES[pool][skill][1][b])
                            out.append({'id':len(out),'pool':pool,'skill':skill,'a':a,'b':b,
                                        'entity':name,'template':tid,'text':text})
    # 3 pools*2 skills*4 combos*8 entities*2 templates =384.
    assert len(out)==384 and len({r['text'] for r in out})==384
    for s in [0,1]:
        assert not set(NAMES['teach'][s])&set(NAMES['selection'][s])
        assert not set(NAMES['teach'][s])&set(NAMES['test'][s])
        assert not set(NAMES['selection'][s])&set(NAMES['test'][s])
    return out

def words(text):return re.findall('[a-z]+',text.lower())

def features(records,hidden):
    teach=np.array([r['id'] for r in records if r['pool']=='teach'])
    skill=np.array([r['skill'] for r in records]); h=hidden.astype(np.float64)
    # Mean/scale use only unlabelled teacher text. Public known task selector.
    model=np.column_stack([h,np.ones(len(h))]);scales={}
    for s in [0,1]:
        ids=teach[skill[teach]==s];allids=np.where(skill==s)[0]
        model[allids,:-1]-=h[ids].mean(0)
        scales[s]=float(np.linalg.norm(model[ids],axis=1).max())
        model[allids]/=scales[s]
    vocab=sorted({w for i in teach for w in words(records[i]['text'])})
    index={w:j for j,w in enumerate(vocab)};bow=np.zeros((len(records),len(vocab)+1))
    for r in records:
        for w in words(r['text']):
            if w in index:bow[r['id'],index[w]]+=1
        bow[r['id'],-1]=1
    bow/=np.maximum(1,np.linalg.norm(bow,axis=1))[:,None]
    attr=np.zeros((len(records),8))
    for r in records:attr[r['id'],4*r['skill']+2*r['a']+r['b']]=1
    return {'model':model,'lexical':bow,'attribute':attr},skill,vocab,scales

def history(seed,records):
    rng=np.random.default_rng(seed)
    rules=[]
    for s in [0,1]:
        v=-np.ones(4,dtype=int);v[rng.choice(4,2,replace=False)]=1;rules.append(v.tolist())
    ids={s:np.array([r['id'] for r in records if r['pool']=='teach' and r['skill']==s]) for s in [0,1]}
    phases=[rng.permutation(ids[s]).tolist() for s in [0,1,0]]
    return {'seed':seed,'rules':rules,'phases':phases}

def labels(H,records,ids,flip0=False):
    out=[]
    for i in ids:
        r=records[int(i)];v=H['rules'][r['skill']][2*r['a']+r['b']]
        out.append(-v if r['skill']==0 and flip0 else v)
    return np.array(out)
