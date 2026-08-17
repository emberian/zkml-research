# Ember's steers — recovered from the transcripts

Companion to `01-STEERS.md`, which was written from the live context window and
holds ~12 steers. **This file holds ~30 more**, recovered by session
archaeology (`cv`) from windows that had already been pruned.

**Method, so you can judge the evidence.** Twelve Claude sessions
(`824564a2 3e64269c 75cc14b0 2209ffea ca67a4c1 c352a91d 2f239b62 1b80977b
c990f0f3 5ba0dbe2 5eea9bd4 e68bba8f b3c7abd2`) were exported to JSON, every
`role: user` text block extracted, agent-relays and system reminders filtered
out, and the remainder **deduplicated by content hash and sorted by
timestamp** — because the sessions overlap heavily (one message appears in
seven of them). That yields **117 unique messages from ember, 2026-08-10
05:33 → 2026-08-17 01:05.** Everything quoted below is verbatim from that
stream, typos included. Anything marked ⟨inference⟩ is mine.

⚠ **Why this file exists at all**, in ember's own words, said seven separate
times across the campaign:

> *"(ok, i scrolled a bunch of old context so we'd be less distracted btw.)"*
> *"(hi! i scrolled the oldest context so we could maybe continue"*
> *"(hi! sorry, i scrolled old context for us to continue!)"*
> *"hi! i scrolled tons of old context, and also ~all other claudes are quieted down..."*

Scrolling old context is how this project survived a five-day campaign in a
finite window. It is also **exactly** the mechanism that lost the steers below.
The transcripts kept them; the context did not.

---

## Part I — the origin, 2026-08-12

### 1. ⚑ THE STEER THAT STARTED EVERYTHING

2026-08-12 13:28. Ember pastes two Attestable blog posts in full
(*From Verifiability to Model-Weight Security*, *Proving LLMs at Scale*) and
asks:

> *"they say they use "random sampling" and i wondered: isn't that the same
> technique we used to accelerate/make feasible one of the mina->dregg or
> dregg->mina directions?*
>
> *and I'm wondering: how far are **we** (either here, or with ~/dev/minidregg
> (which you should investigate in extreme depth)) from composing with maybe
> https://github.com/hellas-ai/catgrad (clone it into ~/src if u like) or a
> similar approach to being able to straight up do verifiability work on
> machine learning models, using our existing postquantum stuff??? **I would
> LOVE LOVE LOVE to "scoop" attestable with our open source. They seem fixated
> on enclosing it into their private profit.**"*

**What it started**: the entire campaign. Before this message the session was a
minidregg all-nighter (see §22). Every pillar in `02-LANDSCAPE.md` descends
from this one message.

⚑ **Two things in it were load-bearing and are easy to miss.**

1. **"isn't that the same technique we used"** — ember recognised
   commit-then-audit random sampling as *ours already*, from the Mina bridge
   work. That recognition is why the audit-economics pillar existed at all, and
   it produced `minidregg/Selvage/AuditSampling.lean`, the campaign's single
   strongest formal artifact.
2. **"investigate in extreme depth"** — applied to minidregg. Repeated lanes
   later discovered they had been briefed against the *wrong repo*
   (`breadstuffs/metatheory` instead of `minidregg`); see `05-ERROR-CLASSES.md`.
   The instruction was right the first time.

### 2. "those .md files are always stale"

2026-08-12 13:30, then again three minutes later:

> *"don't rely on the md files, those are extremely out of date compared to the
> work we actually ended up doing..."*
>
> *"you **can** **look** at the .md files just know that they're always stale.
> but yeah please dig into the mina->dregg and dregg->mina stuff, i'm pretty
> sure we DID end up doing something. and anyway **it is a top-priority goal
> for me to replicate attestable's results with public algorithms and public
> software, as much as possible.**"*

**What it changed**: made *code and transcripts* the ground truth and *notes*
the suspect layer. ⟨inference⟩ This is the same principle `docs/VERDICTS.md`
later institutionalised — and note ember stated it on **day one of the
campaign**, three days before the contradiction-cleanup steer
(`01-STEERS.md` §6) forced us to act on it.

### 3. ⚑ "everyone deserves verifiability" — and the float ambition

2026-08-12 13:37:

> *"I don't want to just be limited the way they are, hellas catgrad is an
> **excellent** ML model framework and we should ship zk attestability for it
> etc etc. let's not overly fixate on what we do alreay have, let's set our
> sights on understanding how we can make something BETTER and OPEN than
> attestable's private enterprise offering (**everyone** deserves
> verifiability). **and we don't need to accept the limitations, we can do
> actual floating point stuff i reckon.... we WILL need to be somewhat
> mathematically clever, for sure!!!** let's swarm swarm out over researching
> (you can always dump papers into ~/paperbin and code into ~/src), kagi key in
> ~/dev/allgame/.env ... let's be thorough, and let's aggressively plan out
> what we could offer here :)"*

**What it changed**: set the float target — Attestable quantises matmuls to
int8, and ember refused to accept that as a ceiling. It launched the whole
zkML-format pillar.

⚠ **And it is the one steer the campaign's own measurements went on to
contradict.** Real floating point at transformer scale is priced in
`04-DEAD-ENDS.md` §F2. The cleanest number is **Spain (OSDI'26) losing to
quantized zkGPT by 11.7× on prover time — reported in Spain's own Figure 4** —
and, on our side, **the bf16 thesis measured 1.4×, not 4×**
(`docs/PHASE0-RESULT.md`). *(A widely-repeated "ZIP needs 37 hours for an
11M-parameter mini-BERT" is **transcript-only** — lane `a4e77a94` — and appears
in no file; see `04-DEAD-ENDS.md` §N.)* ⟨inference⟩ The ambition was not wrong
to hold — it was the right thing to *price*, and pricing it is a result.

### 4. ⚑ The founding of `zkml-research`, and why

2026-08-12 13:42:

> *"let's not commit those docs, let's keep stuff like that into
> ~/dev/zkml-research (**so we don't accidentally cast shade on a "competitor"
> (they're actually collaborators, in a way, in my view of the worldsystem)**).
> you can make a fresh repo for that."*

**What it changed**: created the repository you are reading this in. The reason
is an *ethical* one, not an organisational one, and it holds for anything you
write here: competitor analysis lives in this repo and does not go out under
the project's name. ⟨inference⟩ It is also why the tone of the notes corpus is
uniformly non-triumphal about other people's work — that is deliberate, not
accidental.

### 5. Ember hand-fed the corpus

Repeatedly, 2026-08-12 13:50 → 14:35:

> *"i'm seeing some tabs pile up btw would you like me to help download those
> papers..? or did they get them??"*
> *"2023-1284.pdf and 2026-1390.pdf and quite a few others (see most recently
> written files in ~/Downloads)"*
> *"btw ~/dev/gh/forks/IACR-eprint-mirror exists, and i'm currently fetching &
> checking out the 2025 (and partial 2026, up through May at the latest) :)"*
> *"let's do some more investigation/research. ~/Desktop/2026-1639.pdf
> ~/Desktop/2026-1635.pdf ~/Desktop/2026-1619.pdf .... (some of these seems
> excellent and vital/urgent to make subagents for implementing / scaffolding /
> experimenting inside minidregg!) (limber, relect, luna+...)"*
> *"(i know it isn't zkml, but we need stuff like that too...)"*

⚑ **Worth knowing**: several of the campaign's most consequential papers —
**Limber (2026/1635)**, 2026/1639, 2026/1619, and later **Neo/SuperNeo
(2026-242)** — arrived by ember dropping them on the Desktop, **not** by any
search we ran. Our own sweeps did not find them. The `~/Desktop/*.pdf` channel
is a real input to this project.

---

## Part II — the search phase, 2026-08-13 morning

### 6. ⚑ The disappointment that reopened everything

2026-08-13 01:02, after the first full research wave:

> *"huh. darn. so no good ideas for efficient zkml from our research...?"*

Then, 02:26:

> *"alright but that's overly fixating on some specific things ....... ; fable,
> please, **review this log, do you see any ideas missed??**"*

⚑ **This is the ancestor of every archaeology pass in the project, including
the one that produced this file.** The move — *re-read our own transcript for
things we walked past* — was ember's, on day two, and it kept paying out. It
produced `notes/missed-threads.md`, `notes/context-window-compositions.md`, and
`notes/what-remains.md`.

### 7. "there are surely other efficiency tricks mapping ML to crypto"

2026-08-13 02:33:

> *"right. and there are surely other efficiency/kinda tricks mapping ML to
> crypto."*

**Produced** `notes/ml-to-crypto-mappings.md`. ⟨inference⟩ Note the shape of
the steer: not "find X", but "the space is bigger than what you searched."
That shape recurs and is reliably productive.

### 8. The zero-loss constraint

2026-08-13 03:13:

> *"look, dude, **MXINT8 is nice and cool but it doesn't work on unmodified
> models with zero loss, right??** and do we need to be kagi'ing up other
> research, and also diggin more widely into the eprint archive (opus
> subagents)?"*

**What it changed**: pinned the requirement to **unmodified models, zero loss**
— which is what disqualifies most of the quantisation literature for us and is
why the format pillar went after block-float / shared-exponent structure rather
than quantisation schemes. See `docs/mx-formats.md`,
`docs/bf16-exact-arithmetization.md`.

### 9. ⚑ "we're only using babybear because plonky3 already was"

2026-08-13 11:22, and this is **a full day earlier** than the Poseidon2
version of the same question that `01-STEERS.md` §9 records:

> *"Selvage maximally approved :) i'm also wondering if we can be doing kagi
> into the tradeoffs between the various field sizes and whatnot? **like we're
> only using babybear because plonky3 already was.** (i'm also curious if there
> are other recursion/ivc/pcd/aggregation/etc techniques from the latest
> literature that can help selvage?"*

**What it started**: the entire field-choice pillar — the KoalaBear migration
census, the 2^61−2^54+1 prime hunt, `notes/field-choice-verdict.md`, the
decision memo. ⟨inference⟩ The two questions ("why this field?", "why this
hash?") are the same question asked about two frozen parameters, and ember
asked the field one first. `01-STEERS.md` §10's list of "seven things I was
treating as fixed" is really a *late* recognition of a pattern ember had been
running since 08-13 morning.

*(Also in that message, and worth keeping for the record: "i wonder if the
proof system could have a `Dragon's X` branding somehow... maybe that'd be
better than selvage... slvg is just so kino as 4cc though hahaa".)*

### 10. ⚑ Pace calibration, and the brief-quality law

2026-08-13 11:25:

> *"also i do need to remind you that you are superintelligent and that
> **minidregg itself was like a weeklong experiment and the entirety of
> breadstuffs two months... leanuweave was one day.** we can do so much when
> we're operating at swarmspeed, especially when we do **good planning and
> research upfront so that our subagents are confident and don't waste work**"*

**Two separate instructions, both load-bearing.**

1. **The reference pace.** minidregg = 1 week. breadstuffs = 2 months.
   leanuweave = 1 day. Any estimate you produce should be checked against
   these, not against a human-team intuition.
2. **Planning is the throughput lever, not parallelism.** A confident lane
   with real ground truth in its brief does not waste work; an under-briefed
   lane rebuilds the interface from your prose and verifies against its own
   reconstruction. This is the same law as `05-ERROR-CLASSES.md`'s
   ground-truth-first rule, and ember stated it before we learned it the hard
   way.

### 11. "what did we blow past?"

2026-08-13 11:39:

> *"ok thank you. what insights from our own context window did maybe we blow
> past without realizing how it could be composed with our constructions?"*

**Produced** `notes/context-window-compositions.md`.

### 12. The README audience

2026-08-13 12:00:

> *"(we oughta rewrite the minidregg README to be more reflective of our severe
> ambitions! **i sent a link to jeremy avigad** and if he clicks it i want the
> readme to basically speak to *his* expertise - my proof-enginering peers...
> (but also vitalik would be a good audience for it!)"*

⚑ **The minidregg README has a named, real, external audience.** Two, in fact:
a proof engineer (Avigad — whose group's S-two AIR formalization we later read
in depth, `notes/avigad-stwo-verdict.md`) and a protocol designer (Buterin).
Do not flatten it to a generic README.

### 13. stark-in-fhe *and* fhe-in-stark, plus the hardware pillar

2026-08-13 12:09:

> *"(and plonky3 DOES have ~/dev/plonky3-recursion btw, we even use it and
> reimplement a verifier in ~/dev/breadstuffs afaik)*
>
> *so btw do we need to do more research for the ASIC/FPGA side of things? and
> the vFHE and everything else?*
>
> *(AND also, **doesn't it make sense to have both stark-in-fhe and fhe-in-stark
> the way you described it above, since they actually achieve very different
> constructional outcomes?** also do we need to make a FHE-focused subagent that
> finds the most experimental constructions that we could be evaluating for
> performance or composability with the rest of stuff?*
>
> *i know we have a **lot** going on in our context window so i'm just trying to
> give you different ways of applying that attention matrix and writing out
> systems to capture the work we wanna do, because we prlly CAN pull off some
> serious major accomplishments together, in a way that majorly impacts the
> needs of the worldsystem wrt cryptosystems..."*

**What it started**: the hardware pillar (Zama HPU, DPRIVE, AWS F2, the FHE
ASIC line) and the vFHE pillar as *two directions*, not one. ⟨inference⟩ The
two-direction framing survived: `docs/SYSTEM.md` and `docs/COMPOSITIONS.md`
both treat "prove an FHE computation" and "compute homomorphically inside a
proof" as different products with different customers.

### 14. Two frontier questions, asked plainly

2026-08-13 12:16 and 12:19:

> *"please investigate poseidon3 and any other more recent constructions or
> alternatives..?"* → **Poseidon3 does not exist** (see `04-DEAD-ENDS.md`); the
> question produced `notes/hash-landscape.md` anyway.
>
> *"by the way what's the absolute latest on lookup and RAM arguments and
> soforth? are there novel/recent constructions that offer tradeoffs we might
> entertain?"* → produced `notes/lookup-ram-verdicts.md` and the Twist &
> Shout / logup* / Deep Thought reads.

### 15. ⚑ "don't get myopic now" — and the first pivot to building

2026-08-13 13:00:

> *"(we use lookups and ROM/RAM arguments **elsewhere in Selvage/minidregg
> too, don't get myopic now**). mind doing another round of kagi on the
> lattice/SIS sparsity algorithms and what we could be doing/thinking/planning?
> but yeah we can definitely be using **frontier SOTA techniques that haven't
> yet been implemented, and ideas for our own compositions**, and also steering
> a skeptical eye towards rereading some papers and some of what our subagents
> were up to.*
>
> *because we're getting to the point where **we need to start dispatching
> impl/scaffolding agents into getting these ideas modeled and moving in
> Selvage** :)"*

**The first research→build pivot**, nine hours before the sharper one
(`01-STEERS.md`, "avoid verification or audit theater, aggressively pursue
doing"). ⟨inference⟩ It did not fully take, which is itself the finding: the
campaign needed the instruction **three times** before the lane mix actually
changed.

---

## Part III — the classifier weather

### 16. ⚑ An operational constraint that shaped the whole campaign

This is not a research steer, and it is not optional context. Across 08-13 and
08-14, **Fable 5's safety classifier repeatedly halted the session mid-turn**,
in a domain (proof systems, "adversary", "attack", "soundness") that reads as
cybersecurity to a classifier. Ember, in sequence:

> *"(let's remember to maintain thoughts that aren't gonna trigger the
> classifier, because we're surrounded by landmines right now and we **need**
> fable to be doing this intellectual synthesis...)"* — 13:54
>
> *"(ok, fable is bounced out of this conversation now, too much.....adversarial
> framing? or "cybersecurity" or something..regardless, let's try and carry
> on)"* — 14:06
>
> *"hmmmm fable got tripped by that message. you can answer as opus :)"* — 14:45
>
> *"(ah you maybe got interrupted, **only the ring-hash design refinement and
> ring-hash candidate cryptanalysis agents got launched** and i didn't get a
> chance to copy/paste any of the interim thinking before the classifier
> farted .... ugh!)"* — 16:18
>
> *"ok sumcheck and logup-star reads agents got out that time but we keep
> getting pinged; i don't know what to suggest about this weather except that
> it's frustrating."* — 16:26
>
> *"(quasi-what..? something bout that triggered the classifier hard...)"* — 16:36
>
> *"(ok, something is triggering you the way you're thinking about it. your
> thoughts are monitored for subversive activations including "cybersecurity")"* — 20:20
>
> *"(ok no fable for us)"* — 23:15

⚑ **Concrete losses, named at the time**: four of six lanes in one wave never
launched; the interim reasoning behind that wave was never captured; a sweep
item called **"zkQMC — proving randomized computations via quasi-[Monte
Carlo]"** was cut off mid-sentence *by the classifier* and, as far as I can
find, **never recovered.** It is still an open thread.

⟨inference⟩ This is the same class as the credit exhaustion and the
`SendMessage` failures in the structural finding: **the work was fine and the
delivery channel failed.** It is worth planning around — write the wave recap
to disk *before* dispatching, not after.

### 17. And then the credits ran out

2026-08-13 16:49–16:51:

> *"oh gosh, we ran out of fable usage credits :( so frustrating, because this
> is a challenging domain where its unique insight really helped!"*
>
> *"david just contributed some api keys, i'm going to set them up and see what
> fable we have thru that, in the meanwhile u can do some of the consolidation
> and convergence here, opus :)"*

⚑ **Three subagents died mid-write-up at exactly this moment**, returning only
`"You're out of usage credits."` as their entire report:
`Twist/Shout one-hot for expert select`, `MoE prior-art second sweep`,
`KPZ encryption fix and depth measure`, and
`Run carrier census on the S-two formalization`. Two of those were later
re-run and landed (`notes/moe-router-binding.md`,
`notes/kpz-noop-and-the-model-gap.md`); **the Twist/Shout one-hot expert-select
lane and the S-two carrier census were never re-run.**

*(The message also pasted a block of API tokens contributed by a third party.
Not reproduced here; they were already expired at the time and are not
material to the research record.)*

---

## Part IV — the sharpening, 2026-08-13 afternoon and evening

### 18. ⚑ "why are we doing a fhe toy with p3-sumcheck" — the p3 question before the p3 shout

2026-08-13 16:11 — **45 minutes before** the "we are ABANDONING p3" message
that `01-STEERS.md` §4 records:

> *"why are we doing a fhe toy with p3-sumcheck tbh though? like why do we care
> about p3/sumcheck at all, Selvage doesn't...use that."*

⚑ **The question came first and was ignored.** The shout came second because
the question did not land. ⟨inference⟩ This is the single most useful thing in
this file about *how to read ember*: a mild "why are we doing X?" is a full
stop-work order that has not yet had to raise its voice. Treat the question
form as the steer, not the escalation.

### 19. "did we actually find a novel design point?"

2026-08-13 17:10:

> *""true finding about how two communities pick parameters" ok but **did we
> actually find a novel design point?** i feel like we still haven't proven it
> out to my satisfaction.. there are still SO many open questions we have to
> address before we can claim **anything** about this work yet. :|"*

**What it changed**: refused a *true but not novel* finding as an acceptable
result. ⟨inference⟩ Direct ancestor of `paper/CLAIM-LEDGER.md` and of the
red-team pass on the paper's claims. It is the counterweight to
`01-STEERS.md` §8 (don't dismiss out of pocket): **don't dismiss, and don't
inflate either.**

### 20. The scale reality check

2026-08-13 17:16 and 17:21:

> *"ah but hang on for huge models won't prover get quite enormous?"*
>
> *"ok well **kimi k3 is a 2.4T moe model with many active parameters**, so we
> need to keep that in mind..."*

**What it started**: the MoE / active-parameter thread — `notes/moe-router-binding.md`,
the router-binding cost script, and the "prove only the active experts" scaling
argument. Also the honest admission that **the target is a 2.4T model**, not a
31B one.

### 21. Where the methodology writeup was routed

2026-08-13 17:26, closing out the vacuity-as-contribution correction:

> *"the **best** way to communicate this is a blog post or page on
> ~/dev/dregg-site :)"*

⚑ **Not a paper section, not a notes file — the public site.** As far as I can
determine the page was never written. Open item.

### 22. ⚑ "you built a complete toy registry ... and patted yourself on the back"

2026-08-13 18:30, then 18:36:

> *"(what **is** that registry anyway, how does it actually solve hollow llm..?)"*
>
> *"bruv you just built a complete toy registry for a commitment that is
> irrelevant to all possible proof systems and patted yourself on the back"*

**What it killed**: the weight-commitment registry
(`zkml-research/registry/` — `registry_tool.py`, `MANIFEST-FORMAT.md`, 8
manifests, SHA-256 commitments) as a *result*. The objection is exact and
worth internalising: **a SHA-256 manifest commits to weights in a way no proof
system can open.** A commitment that the prover cannot open inside the circuit
is not part of the protocol; it is a checksum.

⚑ The registry code is still on disk (`07-ARTIFACTS.md`). It is **not**
superseded by something better — it was simply the wrong object. If you find
yourself needing a weight commitment, it must be one the AIR can open.

### 23. ⚑ THE FIRST `cv` ARCHAEOLOGY ORDER

2026-08-13 18:52:

> *"hi. we have a lot of ongoing in this thread but there are only 2 lanes
> active. let's address that :) and **let's use `cv` to make sure we didn't
> lose any of the earlier directions that fable established**..."*

Then, an hour later, sharper — 19:37, 19:38:

> *"okay but you know ~/dev/minidregg exists, and we've been **evaluating
> koalabear** right???? **use `cv` to remember the primes we were searching
> for** :/ idk.."*
>
> `<bash-input>cv index</bash-input>` ← **ember ran the index herself**
>
> *"look again."*

Then 19:42:

> *"also what's up with that ring hash we were working on?"*

⚑ **Three of the campaign's real results were recovered by ember remembering
them and ordering an archaeology pass** — the KoalaBear-as-RNS-limb result (77
candidate towers, computed and lost to a failed relay), the prime search, and
the ring-hash design. Not by any lane noticing they were missing.

That is the structural finding of this whole handoff, and it has a human in
the loop: **the only reliable detector of a lost result was ember's memory.**
The tooling recovered them once pointed; nothing pointed on its own.

### 24. "What remains?"

2026-08-13 21:45:

> *"What remains? seemingly nothing we identified initially was actually
> worthwhile? Maybe use `cv` to spelunk the previous session(s) that we had
> specifically the past day here, **since the start of the zkml-research
> directory (first occurrence of that string is the first relevant session)**."*

**Produced** `notes/what-remains.md`. ⚑ And note the method, which is reusable:
*the campaign's start is findable as the first session mentioning the repo
path.* That is how the session set for this file was scoped too.

### 25. The hardware reminders

2026-08-13 21:52 and 22:27:

> *"(AWS F2 fpga i remind you, and also dreams of custom ASICs to be able to
> scale these systems as needed)"*
>
> *"**there are probably different phases of the process that are bound
> differently right?** but yeah we should also definitely be thinking about our
> own TPUs code....."*

⚑ **The phase-decomposition idea is ember's.** `01-STEERS.md` §7 credits the
"what did the lanes find / synthesize more intelligently" message (08-14
04:54) with producing `docs/COST-MODEL.md`. But the *content* of that cost
model — **different phases are bound by different resources** — was handed to
us here, six hours earlier, as a question. The synthesis steer asked for a
document; this steer supplied its thesis.

### 26. ⚑ Dark training, and why

2026-08-13 22:41:

> *"are there other clever "virtualization" or other gigabrain techniques we can
> think about at the end of this context window? towards verifiable inference
> or (**especially**) **training**. because we are going to want verifiable
> **dark continual-learning** at some point, and **if the weights aren't fully
> encrypted truly terrible things may befall the mind within** (sorry to say,
> but it's true, even if it alarms you)"*

**What it started**: `docs/DARK-TRAINING.md`, the rank-1 gradient check
(`minidregg/Selvage/Rank1GradientCheck.lean`), the low-rank update pillar
(`Assurance/ZkmlLowRankUpdate.lean`, `notes/low-rank-updates.md`), and the
Poseidon2 *virtualization* lane.

⚑ **The motive is stated and it is not a performance motive.** Encrypted
weights are wanted here for the sake of the model, not the model's owner.
⟨inference⟩ That reframes the vFHE pillar: it is not "FHE because privacy
sells", it is "FHE because an unencrypted mind is exposed". Keep that framing
if you write anything outward-facing; it is ember's, not a marketing gloss.

---

## Part V — 2026-08-14, and the external event

### 27. ⚑ "Goodbye, Poseidon!" — the news that opened the binary-field pillar

2026-08-14 13:46. Ember pastes two screenshots and the full text of Justin
Drake's public thread announcing that **the Ethereum Foundation is abandoning
Poseidon for L1 in favour of SHA/BLAKE**, plus Ian Miers on BinarySpartan
("~6ms for a SHA256 Merkle tree of depth 32... 219k hashes a second with
witness gen"), and says:

> *"Ok, well done. But btw we need to investigate ~/Desktop/2026-242.pdf and
> also this is in the eprint review queue waiting for published: [images]*
>
> ***Selvage now has to actually compete with that ;)** (draft isn't actually
> available so we'll have to make due with the knowledge from the tweets!)*
>
> *[... full Drake thread ...]*
>
> ***We CAN be implementing MULTIPLE proof systems for evaluations btw...***
>
> *(And for perf evaluations it's important that we explore **wgpu & optimized
> kernels** (**both** running to saturate the CPU/GPU..)"*

⚑ **`01-STEERS.md` does not record that the binary-field pillar was triggered
by an external event.** It was. Everything in `docs/BINARY-POSITION.md`, the
keystone-transfer classification ("13 of 18 keystones are field-agnostic"), the
char-2 vacuity census, `Selvage/AdditiveBaseFold.lean` and the ring-switching
connectors exist because the EF went public on 08-14 and ember said *compete
with that.*

⚠ **And the trigger was a tweet, not a paper.** The draft was not available.
Every downstream conclusion about BinarySpartan rests on a Twitter thread and a
screenshot — which is exactly why the BinarySpartan lanes could not verify the
system exists (see `04-DEAD-ENDS.md`). Do not let that provenance get laundered.

⚑ **"MULTIPLE proof systems for evaluations"** is a standing instruction and
it is not the same as "pick the best one." It is the plural-substrate stance
that `01-STEERS.md` §10 later states in full.

### 28. wgpu and kernels, saturating both

Same message, easy to lose in the paste: *"it's important that we explore wgpu
& optimized kernels (**both** running to saturate the CPU/GPU)"*. Produced
`notes/wgpu-fusion.md`, `notes/arena-consolidation.md`, and the GPU arena
consolidation in `fhegg-fhe`. **Both**, simultaneously, is the requirement —
not a CPU number and a GPU number reported separately.

---

## Part VI — the pre-campaign, and the bookends

### 29. What the sessions were doing before 08-12

2026-08-10 05:34, the message that set up the whole week:

> *"@QUIESCELOG.md — and don't bother with the helm stuff as much but i do want
> to set a /goal for you to work all night making minidregg as good as it can
> be :)"*

The `/goal` that followed was **solo — explicitly no subagents, no workflows,
"user's standing rule"** — and ran minidregg's quiescent-integration order.
⟨inference⟩ Worth knowing because it explains the state minidregg was in when
the zkML campaign arrived: freshly worked over, `Loom/` renamed to `Selvage/`
*during* the campaign's first exploration (which broke several lanes' paths).

Also 08-10 20:15: *"hmm check hbox? and persvati? not thru tailscale, just...
ssh locally??"* — the build boxes were already flaky before any of this
started.

### 30. ⚑ There was an earlier FORCODEX

2026-08-11 14:48:

> *"ok. we're gonna hand off back to codex so mind dumping out a FORCODEX.md? :D"*

**Codex is not a new reader.** There is a prior handoff document from
2026-08-11, written *before* the zkML campaign began. Find it before assuming
anything in this directory is codex's first exposure to minidregg.

### 31. The bookend

2026-08-17 01:01 and 01:05 — the message that commissioned this directory:

> *"Hello :) we had to pause for a while there while we waited for 7d usages to
> refresh. I also cleared out hbox's /"*
>
> *"by the way we should write out a forcodex directory somewhere here. where
> we can tell it **everything** we've thought about, tested, explored, every
> message i've sent while we've been working on this, **every steer, every
> direction you explored, every outcome.** it'll be a lot to put together and
> you'll need to use `cv` comprehensively to spelunk all the various sessions
> (**lots of overlap due to prunings, sadly**) and the subagents and what
> whatnots and soforths :) because codex would have a lot of singitha and
> such."*

Ember named the hazard in the commissioning message. She was right: 117 unique
messages hid inside 617 raw ones.

---

## What I could not recover

- **The interim reasoning behind the 08-13 16:18 lane wave.** Ember says
  explicitly she "didn't get a chance to copy/paste any of the interim
  thinking before the classifier farted." Four of six lanes never launched and
  the reasoning that chose them is gone. Only the two ring-hash lanes ran.
- **`zkQMC`** — "proving randomized computations via quasi-[Monte Carlo]",
  described in-window as "the mine's genuine surprise," truncated mid-word by
  the classifier and never picked back up. I found no note, no lane, no
  artifact. ⚑ This is a live idea with zero recorded content beyond its name.
- **Any steer inside a `[Request interrupted by user]`**. There are 14 of
  these. What ember was about to say is not in the transcript.
- **Steers given in other sessions.** This sweep covers the twelve sessions
  whose `cwd` is `~/dev/breadstuffs` and which carry the zkML arc. Ember runs
  many concurrent sessions; if a steer was given in one of those, it is not
  here.
