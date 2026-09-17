# Null-perturbation proof modules

[AsymptoticallyIntegerHD/](AsymptoticallyIntegerHD/) contains the proof
applied by the [showcase](../showcase.lean). Start with
[PublicAssembly.lean](AsymptoticallyIntegerHD/PublicAssembly.lean) for the
library theorem. [Basic.lean](AsymptoticallyIntegerHD/Basic.lean) checks its
type in an anonymous example.
[InfiniteAssembly.lean](AsymptoticallyIntegerHD/InfiniteAssembly.lean)
constructs the annihilating witness;
[NonCompleteness.lean](AsymptoticallyIntegerHD/NonCompleteness.lean) derives
the failure of exponential completeness.

[AsymptoticallyIntegerHD.lean](AsymptoticallyIntegerHD.lean) is the aggregate
import for these modules.
