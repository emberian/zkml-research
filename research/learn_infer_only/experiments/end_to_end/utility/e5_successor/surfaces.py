"""Predeclared new public test strings; no model output selects them."""
NAMES=[['Amaranth','Bellis','Celandine','Daphne','Echinacea','Fuchsia','Gaillardia','Helenium'],
       ['Alina','Boris','Clara','Diego','Elena','Florian','Giulia','Henrik']]
CUES=[
 [[['supple leaf blades','unyielding leaf blades'],
   ['plenty of water in the root zone','very little water in the root zone']],
  [['leaves that can be bent with little force','leaves that are difficult to bend'],
   ['soil that remains drenched','soil that has dried out completely']]],
 [[['somebody you already know well','somebody you have not met'],
   ['a highly ceremonial public gathering','an informal weekend outing']],
  [['a contact with an established personal relationship','a contact with whom you have no shared history'],
   ['a function where official etiquette is expected','a gathering with no expectation of ceremony']]]]
TEMPLATES=[
 ['Assess the care needs of {name}. Leaf condition: {a}. Root condition: {b}. Required class:',
  'The plant named {name} has {a}. Its roots are surrounded by {b}. Assign its care class:'],
 ['For a message addressed to {name}, consider that this is {a}. It concerns {b}. Required class:',
  'At {b}, correspondence must be prepared for {name}, {a}. Assign the message class:']]
def make_records(original,oldmodules,previous):
 for s in [0,1]:
  oldnames={x for m in oldmodules for p in m.NAMES for x in m.NAMES[p][s]}|set(previous.NAMES[s])|{'Marigold'}
  oldtemplates={x for m in oldmodules for p in m.TEMPLATES for x in m.TEMPLATES[p][s]}|set(previous.TEMPLATES[s])
  oldcues={x for m in oldmodules for p in m.CUES for pair in m.CUES[p][s] for x in pair}
  oldcues|={x for template in previous.CUES[s] for pair in template for x in pair}
  newcues=[x for template in CUES[s] for pair in template for x in pair]
  assert set(NAMES[s]).isdisjoint(oldnames) and set(TEMPLATES[s]).isdisjoint(oldtemplates)
  assert set(newcues).isdisjoint(oldcues) and len(set(newcues))==len(newcues)
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
