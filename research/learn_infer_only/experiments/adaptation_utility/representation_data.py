"""Fresh public synthetic surface forms for the preregistered representation study."""
NAMES={
 'teach':[['Acacia','Begonia','Camellia','Dogwood','Elder','Freesia','Gardenia','Hibiscus'],
          ['Anna','Ben','Cara','Damon','Eva','Finn','Greta','Hugo']],
 'selection':[['Ipomoea','Jacaranda','Kerria','Lobelia','Magnolia','Nerium','Oxalis','Peony'],
              ['Ian','Juno','Kara','Liam','Mira','Noel','Opal','Petra']],
 'test':[['Rudbeckia','Salvia','Tamarisk','Ursinia','Verbena','Wisteria','Yucca','Zinnia'],
         ['Rosa','Seth','Talia','Ugo','Vera','Wade','Xena','Yuri']]}
CUES={
 'teach':[[['flexible leaves','hard leaves'],['soggy soil','desiccated soil']],
          [['a longtime acquaintance','a person never met before'],['an awards banquet','a laid-back barbecue']]],
 'selection':[[['limber foliage','solid foliage'],['soil rich in moisture','soil depleted of moisture']],
              [['a trusted associate','a complete newcomer'],['a dignified inauguration','a friendly backyard party']]],
 'test':[[['bendable greenery','inflexible greenery'],['muddy ground','drought-stricken ground']],
         [['a recognizable colleague','an anonymous outsider'],['a diplomatic function','a low-key cookout']]]}
TEMPLATES={
 'teach':[['Inspect {name} for plant care: {a} grow above {b}. Category:',
           'Care file: specimen {name} exhibits {a}, and the roots sit in {b}. Category:'],
          ['Messaging file: {name} is {a} at {b}. Category:',
           'Plan a letter to {name} for {b}; the person is {a}. Category:']],
 'selection':[['The gardener asks about {name}, with {a} over {b}. Care category:',
               'For specimen {name}, the facts are {a} and {b}. Gardening category:'],
              ['Communication with {name}, {a}, happens during {b}. Letter category:',
               'A written greeting is for {name}; occasion: {b}; relationship: {a}. Category:']],
 'test':[['Choose the treatment for {name}: {a} sit atop {b}. Plant category:',
          'Horticultural record {name}: visible {a}; underneath, {b}. Treatment category:'],
         ['Determine the wording for {name} at {b}, knowing the addressee is {a}. Message category:',
          'There is {b}. Send a note to {name}, who is {a}. Correspondence category:']]}

def make_records():
    from text_transfer_data import NAMES as OLDN,TEMPLATES as OLDT,CUES as OLDC
    out=[]
    for skill in [0,1]:
        for table,old in [(NAMES,OLDN),(TEMPLATES,OLDT)]:
            newall=[v for pool in table for v in table[pool][skill]]
            oldall=[v for pool in old for v in old[pool][skill]]
            assert len(newall)==len(set(newall)) and set(newall).isdisjoint(oldall)
        newcues=[v for pool in CUES for pair in CUES[pool][skill] for v in pair]
        oldcues=[v for pool in OLDC for pair in OLDC[pool][skill] for v in pair]
        assert len(newcues)==len(set(newcues)) and set(newcues).isdisjoint(oldcues)
    for pool in ['teach','selection','test']:
        for skill in [0,1]:
            for a in [0,1]:
                for b in [0,1]:
                    for name in NAMES[pool][skill]:
                        for tid,template in enumerate(TEMPLATES[pool][skill]):
                            out.append({'id':len(out),'pool':pool,'skill':skill,'a':a,'b':b,
                              'entity':name,'template':tid,'text':template.format(name=name,
                              a=CUES[pool][skill][0][a],b=CUES[pool][skill][1][b])})
    assert len(out)==384 and len({r['text'] for r in out})==384
    return out
