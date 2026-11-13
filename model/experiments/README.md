# Experiments of the audit

Each folder and each JSON file here is the record of one run of the audit of October 2026. A record is
evidence for one finite run. It is not a proof, and it is not a result for the whole game.

## Files that are not here

`cursor-cycle-source/request.json.gz` and `cursor-cycle-source/request-template.json` are not in this
repository. They hold the complete page, the style sheets and the parsed scripts of the game, and the
notice of the game asks not to re-host its code. `cursor-cycle-source/MANIFEST.json` has their SHA-256
digests. With an installed copy of the game, the audit machine made them with
`cursor-cycle-source/generate-request.mjs`, which reads the template. Without the template, a reader
cannot make the request again, and `build.py` and `run.py` of that folder do not run.

## Paths of the audit machine

On 13 November 2026, for publication, the absolute paths of the audit machine in two scripts became paths
in the repository: `veil-seed-cover/preflight.mjs` and `veil-seed-cover/free-veils.mjs`. The three records
that hold the digests of these scripts have the new digests and a note with the original digests. No
result was calculated again.

A witness file in `model/` records the path of the game engine with `~` for the home folder.
