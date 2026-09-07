-- Ramtastic — formal mathematics in Lean 4.
-- Zero sorry. Zero custom axioms.
-- Author: C. Forrester (Adauriel)
--
-- Public root. Imports the released Tower (standard machinery + bare
-- problem statements) and the Bass Theorem. The full grand-unified root
-- lives in Ramtastic_Vega.lean (gitignored — not released).

import Ramtastic.Bass.HingeRotation
import Ramtastic.BSD.ArithmeticGAGA
import Ramtastic.BSD.BSDFormula
import Ramtastic.BSD.EllipticCurve
import Ramtastic.BSD.HeightPairing
import Ramtastic.BSD.Kolyvagin
import Ramtastic.BSD.LFunction
import Ramtastic.BSD.MordellWeil
import Ramtastic.BSD.Statement
import Ramtastic.BSD.TateShafarevich
import Ramtastic.ChowGroups.AlgebraicCycle
import Ramtastic.ChowGroups.ChowGroup
import Ramtastic.ChowGroups.ChowRing
import Ramtastic.ChowGroups.IntersectionProduct
import Ramtastic.ChowGroups.ProjectiveSpace
import Ramtastic.ChowGroups.RationalEquivalence
import Ramtastic.ComplexStructure.AlmostComplex
import Ramtastic.ComplexStructure.DelDelBar
import Ramtastic.ComplexStructure.Integrability
import Ramtastic.ComplexStructure.TypeDecomposition
import Ramtastic.CycleClass.CycleClassMap
import Ramtastic.CycleClass.FundamentalClass
import Ramtastic.CycleClass.ImageInHodge
import Ramtastic.CycleClass.RingHomomorphism
import Ramtastic.CycleClass.ThomClass
import Ramtastic.DeRham.ClosedExact
import Ramtastic.DeRham.DeRhamTheorem
import Ramtastic.DeRham.DifferentialForms
import Ramtastic.DeRham.Functoriality
import Ramtastic.DeRham.LeibnizRule
import Ramtastic.DeRham.LongExactSequence
import Ramtastic.DeRham.ManifoldForms
import Ramtastic.DeRham.Quotient
import Ramtastic.DeRham.StokesTheorem
import Ramtastic.DeRham.WedgeProduct
import Ramtastic.Dolbeault.DolbeaultCohomology
import Ramtastic.Dolbeault.DolbeaultComplex
import Ramtastic.Dolbeault.DolbeaultTheorem
import Ramtastic.GAGA.AnalyticSheaves
import Ramtastic.GAGA.ChowToHodge
import Ramtastic.GAGA.GAGACorrespondence
import Ramtastic.GAGA.ProjectiveKahler
import Ramtastic.GAGA.RationalHodgeStructure
import Ramtastic.HardyLittlewood.PrimePairAsymptotic
import Ramtastic.HardyLittlewood.Tower
import Ramtastic.HodgeStar.Codifferential
import Ramtastic.HodgeStar.HodgeLaplacian
import Ramtastic.HodgeStar.L2InnerProduct
import Ramtastic.HodgeStar.StarConstruction
import Ramtastic.HodgeStar.StarOperator
import Ramtastic.Kahler.HardLefschetz
import Ramtastic.Kahler.HodgeDecomposition
import Ramtastic.Kahler.KahlerForm
import Ramtastic.Kahler.KahlerLaplacian
import Ramtastic.Kahler.LefschetzOperator
import Ramtastic.Kahler.SL2Weight
import Ramtastic.Polignac.Statement
import Ramtastic.PrincipalBundles.Connection
import Ramtastic.PrincipalBundles.PrincipalBundle
import Ramtastic.QuantumYM.CompactGroupProduct
import Ramtastic.QuantumYM.GlimmJaffeLimit
import Ramtastic.QuantumYM.StrongResolventConvergence
import Ramtastic.QuantumYM.WilsonActionConstruction
import Ramtastic.SchurTest
import Ramtastic.SeibergWitten.CliffordBundle
import Ramtastic.Sobolev.CartanProof
import Ramtastic.Sobolev.CompactManifold
import Ramtastic.Sobolev.EllipticOperator
import Ramtastic.Sobolev.EllipticRegularity
import Ramtastic.Sobolev.FredholmTheory
import Ramtastic.Sobolev.HodgeTheorem
import Ramtastic.Sobolev.SobolevSpaces
import Ramtastic.Tao.BoundedPrimeGaps
import Ramtastic.Tao.Tower
import Ramtastic.TwinPrimes.Statement
import Ramtastic.TwinPrimes.Tower
