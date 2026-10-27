module

public import CFSG.Certificates.Kernel.J4Q.MatSound
public import Certificates.Kernel.J4Q.MatData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Th.S.Chars

public section

set_option maxRecDepth 400000

#th_chars CFSG.KD.J4Q.LA CFSG.Sporadic.J4.Native.seedA
#th_chars CFSG.KD.J4Q.LB CFSG.Sporadic.J4.Native.seedB

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native

@[expose] noncomputable def matData : MatData where
  c := c
  rm := rm
  one := one
  pad := pad
  t0 := t0
  t1 := t1
  t2 := t2
  t3 := t3
  t4 := t4
  t5 := t5
  t6 := t6
  LA := LA
  LB := LB
  A := A
  B := B
  Ai := Ai
  Bi := Bi
  L := [L0, L1, L2]
  Li := [L0i, L1i, L2i]
  C := C
  Ci := Ci
  F := F

theorem consts_ok : matData.consts = true := by quickRfl

theorem seeds_ok : matData.seeds = true := by quickRfl

theorem invs_ok : matData.invs = true := by quickRfl

theorem loc_ok : matData.loc = true := by quickRfl

theorem pows_ok : matData.pows = true := by quickRfl

theorem conj_ok : matData.conj = true := by quickRfl

theorem form_ok : matData.form = true := by quickRfl

theorem hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6 := consts_ok

theorem loc_gens (k : Nat) : WfA ((locMats ())[k]?.getD (idRows ())) ∧
    encR ((locMats ())[k]?.getD (idRows ())) = getN one [L0, L1, L2] k :=
  (gens_enc matData LA_eq LB_eq consts_ok seeds_ok invs_ok loc_ok).2.2.1 k

theorem loc_invs (k : Nat) : WfA ((locInvs ())[k]?.getD (idRows ())) ∧
    encR ((locInvs ())[k]?.getD (idRows ())) = getN one [L0i, L1i, L2i] k :=
  (gens_enc matData LA_eq LB_eq consts_ok seeds_ok invs_ok loc_ok).2.2.2 k

theorem base_gens (k : Nat) : WfA (baseMats[k]?.getD (idRows ())) ∧
    encR (baseMats[k]?.getD (idRows ())) = getN one [A, B] k :=
  (gens_enc matData LA_eq LB_eq consts_ok seeds_ok invs_ok loc_ok).1 k

theorem base_invs (k : Nat) : WfA (baseInvs[k]?.getD (idRows ())) ∧
    encR (baseInvs[k]?.getD (idRows ())) = getN one [Ai, Bi] k :=
  (gens_enc matData LA_eq LB_eq consts_ok seeds_ok invs_ok loc_ok).2.1 k

theorem matFacts : CFSG.Sporadic.J4.MatFacts :=
  matFacts_sound matData LA_eq LB_eq consts_ok seeds_ok invs_ok loc_ok pows_ok conj_ok form_ok

end CertificateChecks.KernelJ4Q

end
