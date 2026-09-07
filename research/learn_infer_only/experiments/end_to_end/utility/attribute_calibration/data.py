"""Fixed new public synthetic test surfaces; no outcomes select these strings."""
NAMES=[['Astrantia','Borage','Cosmos','Delphinium','Eryngium','Foxglove','Geranium','Hyssop'],
       ['Alice','Bruno','Celia','Dorian','Esther','Felix','Gemma','Hector']]
# [route][template][attribute][value]
CUES=[
 [[['leaves yielding easily when bent','leaves resisting any bend'],
   ['earth saturated after watering','earth lacking water and crumbling']],
  [['foliage that folds without resistance','foliage that stays firm under pressure'],
   ['a thoroughly soaked root bed','a root bed that has become powdery from thirst']]],
 [[['a companion known for many years','a visitor with no prior acquaintance'],
   ['an event demanding ceremonial etiquette','an easygoing meal with friends outdoors']],
  [['a person you have spent years getting to know','a person you are meeting for the first time'],
   ['an occasion governed by strict social protocol','an occasion where everyone is free to dress and act casually']]]]
TEMPLATES=[
 ['A care decision is needed for {name}. The two observations are {a} and {b}. Assign the plant-care class:',
  'In the nursery report on {name}, the root environment is {b}; above it is {a}. Select the care classification:'],
 ['Compose a suitable message for {name}, {a}. The setting is {b}. Assign the correspondence class:',
  'During {b}, you will write to {name}. This recipient is {a}. Select the communication classification:']]

def make_new_records(old_records, old_modules):
    for s in [0,1]:
        oldnames={x for m in old_modules for pool in m.NAMES for x in m.NAMES[pool][s]}
        oldtemplates={x for m in old_modules for pool in m.TEMPLATES for x in m.TEMPLATES[pool][s]}
        oldcues={x for m in old_modules for pool in m.CUES for pair in m.CUES[pool][s] for x in pair}
        newcues=[x for template in CUES[s] for pair in template for x in pair]
        assert set(NAMES[s]).isdisjoint(oldnames|{'Marigold'})
        assert set(TEMPLATES[s]).isdisjoint(oldtemplates)
        assert set(newcues).isdisjoint(oldcues) and len(newcues)==len(set(newcues))
    records=[dict(r) for r in old_records if r['pool']!='test']
    assert len(records)==256
    for skill in [0,1]:
        for a in [0,1]:
            for b in [0,1]:
                for name in NAMES[skill]:
                    for t,template in enumerate(TEMPLATES[skill]):
                        records.append({'id':len(records),'pool':'test','skill':skill,'a':a,'b':b,
                          'entity':name,'template':t,'text':template.format(name=name,
                          a=CUES[skill][t][0][a],b=CUES[skill][t][1][b])})
    assert len(records)==384 and len({r['text'] for r in records})==384
    assert {r['text'] for r in records[256:]}.isdisjoint(r['text'] for r in old_records)
    return records
