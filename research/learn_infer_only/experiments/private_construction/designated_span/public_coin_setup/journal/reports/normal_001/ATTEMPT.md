# Initial wrapper launch stopped before registration

[EXECUTED] The normal_001 command in stdout/stderr ran params successfully,
then auth-init raised FileExistsError because setup_join.py had precreated its
registration directory. The unchanged adapter creates this directory itself.
No registration keys, public samples, setup context, service or journal event
was generated. commands.jsonl retains the exact command output.

[DERIVED correction] The successor wrapper removes only registration from its
precreated private-role directory list. source_snapshot/ preserves every source
byte named by execution_pins.json at this failed attempt; those pins are resolved
against that historical snapshot. Frozen adapter and journal sources are unchanged.
Fresh normal_002 is a deliberate corrected launch, not automatic partial resume.
