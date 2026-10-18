import LeanItsdangerous.APIs
import LeanItsdangerous.Proofs
import LeanItsdangerous.Proofs.Verified

/-!
# LeanItsdangerous

A clean-room port of itsdangerous to Lean 4: HMAC-signed and timestamped payloads (Signer, TimestampSigner) with a proved signature-format round trip.

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      structures and inductives; invariants are fields
* `RepoImpl/`       the executable definitions; total, structural recursion
* `Specifications/` the properties, stated in `Prop`
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           what users call; returns refinements `{r // Post r}`
-/
