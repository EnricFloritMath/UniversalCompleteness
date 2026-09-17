import Theorem12.PublicAssembly

example (alpha : ℝ) (beta : ℚ) (hAlpha : Irrational alpha)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) :
    Theorem12.Theorem12Conclusion alpha beta :=
  Theorem12.theorem_1_2 alpha beta hAlpha hbeta0 hbetaSmall
