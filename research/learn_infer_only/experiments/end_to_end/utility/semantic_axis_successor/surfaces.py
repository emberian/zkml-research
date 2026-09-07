"""New fixed public stimuli, frozen before any new model score."""
NAMES=[['Achillea','Campanula','Cleome','Dianthus','Gazania','Liatris','Nigella','Scabiosa'],
 ['Adrian','Bianca','Cedric','Dalia','Emil','Fiona','Gideon','Helena']]
CUES=[
 [[['leaf blades that bend readily','leaf blades that stay rigid when bent'],
   ['root soil holding a large amount of water','root soil with almost no water left']],
  [['foliage with little resistance to bending','foliage with strong resistance to bending'],
   ['soil whose water content is high','soil whose water content is low']]],
 [[['someone the sender has known for a long time','someone the sender has never encountered'],
   ['a gathering conducted according to formal protocol','a gathering where casual behavior is welcome']],
  [['an addressee already personally familiar to the writer','an addressee entirely new to the writer'],
   ['an occasion organized with ceremonial rules','an occasion organized as a relaxed social meetup']]]]
TEMPLATES=[
 ['Botanical intake for {name}: the specimen has {a}. Below the surface there is {b}. Decide the care label:',
  'Garden assessment of {name}: {b} surrounds the roots, and the plant displays {a}. Requested care label:'],
 ['A written message to {name} concerns {b}. The recipient is {a}. Decide the communication label:',
  'Correspondence assessment: {name} is {a}; the event is {b}. Requested message label:']]
def make_records(original,oldmodules,prior_modules):
 for s in [0,1]:
  names={x for m in oldmodules for p in m.NAMES for x in m.NAMES[p][s]}
  templates={x for m in oldmodules for p in m.TEMPLATES for x in m.TEMPLATES[p][s]}
  cues={x for m in oldmodules for p in m.CUES for pair in m.CUES[p][s] for x in pair}
  for m in prior_modules:
   names.update(m.NAMES[s]);templates.update(m.TEMPLATES[s])
   cues.update(x for template in m.CUES[s] for pair in template for x in pair)
  newcues=[x for template in CUES[s] for pair in template for x in pair]
  assert set(NAMES[s]).isdisjoint(names|{'Marigold'})
  assert set(TEMPLATES[s]).isdisjoint(templates) and set(newcues).isdisjoint(cues)
  assert len(set(newcues))==len(newcues)
 records=[dict(r) for r in original if r['pool']!='test'];assert len(records)==256
 for s in [0,1]:
  for a in [0,1]:
   for b in [0,1]:
    for name in NAMES[s]:
     for t,template in enumerate(TEMPLATES[s]):
      records.append({'id':len(records),'pool':'test','skill':s,'a':a,'b':b,'entity':name,'template':t,
       'text':template.format(name=name,a=CUES[s][t][0][a],b=CUES[s][t][1][b])})
 assert len(records)==384 and len({r['text'] for r in records})==384
 return records
