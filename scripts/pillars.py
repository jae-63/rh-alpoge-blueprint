# Map a module path to a "pillar" (coarse area of the proof).
RULES = [
    ("Analytic core", ["Formalism.SharpRestriction", "Development.AutomorphicArithmetic.CharacterBoxes",
                       "Development.AutomorphicArithmetic.PrimitiveCosets", "Development.AutomorphicArithmetic.CoprimeRanks",
                       "Formalism.GammaFactorNonvanishing", "Formalism.Statement", "Supplements"]),
    ("Theta correspondence", ["Development.AutomorphicArithmetic.ThetaCorrespondence",
                              "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval"]),
    ("Galois reps & local Langlands", ["Development.AutomorphicArithmetic.Foundations"]),
    ("Modularity / Sha window (VWin)", ["Development.AutomorphicArithmetic.AutomorphicVarieties"]),
    ("Other automorphic arithmetic", ["Development.AutomorphicArithmetic"]),
    ("Weil bound", ["Development.WeilBound"]),
    ("Automorphic spectrum", ["Development.AutomorphicSpectrum"]),
    ("Abelian varieties", ["Development.AbelianVarietyTheory"]),
    ("Heights & Arakelov positivity", ["GroundTheory.HeightsAndTheta", "PositivityTheory"]),
    ("Resolution of singularities", ["Development.ResolutionOfSingularities"]),
    ("Lattices & local-to-global", ["Formalism.LocalToGlobal"]),
    ("Other Formalism", ["Formalism"]),
    ("Other Development", ["Development"]),
    ("Foundations (Ground/Reciprocity/Companion)", ["GroundTheory", "ReciprocityTheory", "CompanionTheory", "Lemmata"]),
]
def pillar(mod):
    for name, pre in RULES:
        for p in pre:
            if mod == p or mod.startswith(p + "."):
                return name
    return "Other"
