# Repeated delivery of accepted revisions

[EXECUTED] The same recipient now reads successive accepted model publications
under separate delivery IDs. The [bounded demonstration](REPORT.md) read
revisions 4 and 6 with recipient 0, retained both receipts, and replayed the
first receipt after the head advanced without invoking the key again. The
frozen parent service and `normal001` runtime remain unchanged.

[DERIVED] `delivery.py` adds two reusable commands. Use the parent's existing
Python environment and a continuing instance whose public journal is current:

```sh
$RING_PY -B delivery.py request --root "$INSTANCE" --coordinate 0 \
  --request-id query-007 --delivery-id delivery-007 \
  --models "$INSTANCE/public/accepted_model_000007.json" > request-007.json

$RING_PY -B delivery.py deliver --root "$INSTANCE" --request request-007.json
```

`request` reads only public metadata and prints the exact request. `deliver`
retains its records in `INSTANCE/deliveries/DELIVERY_ID/` and prints a result
whose status is `delivered` or `replayed`. For a new accepted publication,
create a new request/delivery ID pair. Resubmit the unchanged request file for
an exact retry. Changing either ID or any other request binding while reusing
the other ID refuses. A new ID pair cannot freshly read a stale head.

[DERIVED configuration] Before first use, the instance's trusted local setup
must provide `delivery_credentials.json` containing its canonical genesis
digest and absolute credential-root path:

```json
{"genesis":"<digest of the canonical genesis object>","credential_root":"<absolute instance path>"}
```

Normally the credential root is the same instance. It supplies the already
registered `private/recipient_XX/key.ring` path and the existing
`profiles/recipient_XX.sb`. The demo explicitly names the frozen original
credential root because its public checkpoint is isolated. The configuration
does not copy or contain a key. The worker checks the actual key's registered
coordinate, setup, registry and A context before the unchanged decoder runs.

[DERIVED] The launcher reads public metadata only. It starts the recipient
worker under that recipient's existing sandbox profile; the unchanged transport
query process inherits that profile. The `worker` subcommand is an internal
entry point and should not be invoked bare, because bare invocation does not
install the OS profile.

[DERIVED retry boundary] A durable `running` record is created before launching
the key actor. An interrupted attempt is reported as incomplete and is not
automatically executed again. This explicit refusal handles uncertainty; it
does not prove exactly-once physical execution or recover every power-loss
case. [CONTRACT.md](CONTRACT.md) defines the complete retry and ordering rules.

[SCOPE] The local journal and delivery ledger are trusted. The same fixed key
still works outside this service on retained inputs and allowed combinations;
this extension adds no cryptographic history restriction, new key scope or
hardness claim. The demo imported prior accepted public records rather than
performing new teachings, encryption or setup. No original private key payload
was opened by the orchestration code.
