import Lean4Lean.Theory.Typing.Confluence.StructureMajor

/-! # The confluence parameters of a well-formed environment

`VEnv.WF.params`: the `Params` instance of the confluence engine (`ChurchRosser.lean`) for a
well-formed environment, with its recursor registry (`recursorRegistry`) and its pattern table
(`ConcretePattern`). Every field is a theorem. -/

namespace Lean4Lean.VEnv
open InductiveSignature

/-- **The confluence parameters of a well-formed environment** at universe bound `U`: its
recursor registry and its pattern table (`ConcretePattern`). Every field is a theorem. -/
@[instance_reducible] noncomputable def WF.params {env : VEnv} (henv : env.WF) (U : Nat) :
    Params where
  env := env
  henv := henv
  univs := U
  recursorData := env.recursorRegistry
  recursorData_registered h :=
    ⟨(recursorRegistry_entry h).registered, (recursorRegistry_entry h).name_eq⟩
  Pat := ConcretePattern env
  pat_storedRule h := ConcretePattern.origin henv h
  pat_recursor h := ConcretePattern.recursor henv h
  pat_simple h := ConcretePattern.simple henv h
  pat_uniq h h' hs hi := ConcretePattern.uniq henv h h' hs hi
  pat_wf hΓ h hm ht hc := ConcretePattern.sound henv hΓ h hm ht hc
  pat_app_l h hs := ConcretePattern.app_l henv h hs
  pat_app_l_uniq h h' hs hs' hb := ConcretePattern.app_l_uniq henv h h' hs hs' hb
  pat_app_uniq h h' hs hs' hl hr := ConcretePattern.app_uniq henv h h' hs hs' hl hr
  pat_const_not_unfolding h := ConcretePattern.const_not_unfolding henv h
  recursorData_quot hq := ConcretePattern.recursor_quot henv hq
  pat_ctor_rigid h := ConcretePattern.ctor_rigid henv h
  projection_ctor_rigid hl := henv.projectionCtorRigid hl
  pat_struct_major h hΓ hl hs hlen := ConcretePattern.struct_major henv h hΓ hl hs hlen
  pat_iota_params h hl hcc hm hm' hps hps' :=
    ConcretePattern.iota_params henv h hl hcc hm hm' hps hps'

end Lean4Lean.VEnv
