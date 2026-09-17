# Imported one-dimensional module

[SpectralGapsPrelim/Theorem112/](SpectralGapsPrelim/Theorem112/) contains the
one-dimensional exponential-independence result and its setup. The
higher-dimensional proof imports
`SpectralGapsPrelim.Theorem112.ExponentialIndependence` from this directory.

The [lakefile.lean](../../lakefile.lean) configures this source directory so
the Lean import names remain valid. For the public statements,
begin at [showcase.lean](../../showcase.lean).
