# Resume

[DERIVED] The parent imports `codec.pack_values`, `codec.unpack_values`
and `codec.payload_bytes`, supplies the exact width/count/bound, and
fully consumes the iterator before accepting the container. It should
preserve the runtime source freeze through its actual transport run.

[EXECUTED] Existing cheap controls and the one public-data measurement are
in `MEASUREMENTS.json`; no repeated benchmark grid is needed.

[OPEN] Review the parent's header canonicality, declared lengths, trailing
bytes, parameter/context binding, signed mapping and process access boundary
using its own artifacts. This helper does not establish those properties.
