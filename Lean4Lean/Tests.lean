import Lean4Lean.Tests.Toolchain
import Lean4Lean.Tests.ProjectionInference
import Lean4Lean.Tests.ProjectionWithoutCasesOn
import Lean4Lean.Tests.ProjectionSpecialization
import Lean4Lean.Tests.ProjectionReduction
import Lean4Lean.Tests.ShapeDecide
import Lean4Lean.Tests.IotaShape
import Lean4Lean.Tests.InductiveSignature
import Lean4Lean.Tests.InductiveRestoration
import Lean4Lean.Tests.InductiveCompilation
import Lean4Lean.Tests.SortEquationRejection
import Lean4Lean.Tests.SpecializedRecursorShape
import Lean4Lean.Tests.Environment
import Lean4Lean.Tests.RecursiveInductive
import Lean4Lean.Tests.NestedInductive
import Lean4Lean.Tests.NestedConstructorRoundTrip
import Lean4Lean.Tests.NestedIndexedFamily
import Lean4Lean.Tests.NestedRecursorReduction
import Lean4Lean.Tests.KNormalization
import Lean4Lean.Tests.UnitLikeK
import Lean4Lean.Tests.KernelHardening
import Lean4Lean.Tests.LevelStd
import Lean4Lean.Tests.RecursorOracle
import Lean4Lean.Tests.DeclFVar
import Lean4Lean.Tests.Level
import Lean4Lean.Tests.TypeAnnotationWrappers
import Lean4Lean.Tests.StructEtaIota
import Lean4Lean.Tests.CacheScope
import Lean4Lean.Tests.FVarRenamingEquivManager
import Lean4Lean.Tests.QuotInit
import Lean4Lean.Tests.Replay
import Lean4Lean.Tests.AmbientContext
import Lean4Lean.Tests.RecursiveFieldClassification
-- Tests that do not build yet are added back with the wave that makes their imports build
-- (`iota-port/PLAN-RECONCILED.md`):
-- wave 2: InductiveTheory and TypedInductiveCompilation (re-expressed for the structure
--   `VInductDecl.WF` and `VEnv.pats`), CorruptRecursorMetadata (`Verify.Inductive.Recursor`)
-- wave 3: CorruptRestoredRecursorMetadata (`Verify.Inductive.Nested`)
-- wave 4: PreludeEq (`Verify.Inductive.Prelude.EqSyntax` of wave 2; `VEnv.HasCanonicalEq` is
--   needed only by confluence)
-- dropped: CacheMode, SyntacticTranslation (the scoped cache mode and the strengthening study)
