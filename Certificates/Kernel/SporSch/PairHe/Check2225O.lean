module

public import Certificates.Kernel.SporSch.PairHe.Check2225
public import Certificates.Kernel.SporSch.PairHe.OrbFns
public import CFSG.Certificates.Kernel.SporSch.PairHeOrbSound
public import CFSG.Certificates.Kernel.SporSch.PairHeOrbCount

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PHePart

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Certificates
open CFSG.Certificates.Native CFSG.Sporadic.HeldB
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSporSch.PJ3Group CertificateChecks.KernelSporSch.PHSClass
open CertificateChecks.KernelSporSch.PHeCount

section He

theorem blkAll {G R B : Nat} {f : Nat → Bool}
    (h : ∀ g < G, ∀ r < R, allBlk (Nat.mul (Nat.add (Nat.mul g R) r) B) f B = true) (hB : 0 < B)
    (hR : 0 < R) {q : Nat} (hq : q < G * R * B) : f q = true := by
  have h1 : q / B < G * R := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm B]; exact hq)
  have h2 : q / B / R < G := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm R]; exact h1)
  have h3 := allBlk_spec (h (q / B / R) h2 (q / B % R) (Nat.mod_lt _ hR)) (q % B) (Nat.mod_lt _ hB)
  have e : Nat.add (Nat.mul (Nat.add (Nat.mul (q / B / R) R) (q / B % R)) B) (q % B) = q := by
    change (q / B / R * R + q / B % R) * B + q % B = q
    rw [Nat.div_add_mod' (q / B) R, Nat.div_add_mod' q B]
  rwa [e] at h3

theorem bs_lt {b : Nat} (hb : b ∈ PairHe.bs) : b < 5 := by
  have e : PairHe.bs = [0, 1, 2, 3, 4] := rfl
  rw [e] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  omega

theorem op_pt (hop : PHeCn.opB = true) {m : Nat} (hm : m < 17) :
    fld(PHeO.OP, Nat.mul 14 m, mask 14) < 8330 := by
  unfold PHeCn.opB at hop
  rw [bAnd_iff] at hop
  have h := allBlk_spec hop.1 m hm
  have e : Nat.add 0 m = m := Nat.zero_add m
  rw [e, bAnd_iff] at h
  simpa [Nat.blt_eq] using h.1

theorem op_mb (hop : PHeCn.opB = true) {b : Nat} (hb : b < 5) :
    fld(2636832, Nat.mul 5 b, mask 5) < 17 := by
  unfold PHeCn.opB at hop
  rw [bAnd_iff, bAnd_iff, bAnd_iff] at hop
  have h := allBlk_spec hop.2.2.1 b hb
  have e : Nat.add 0 b = b := Nat.zero_add b
  rw [e, bAnd_iff] at h
  have e5 : mask 5 = 31 := rfl
  rw [e5]
  simpa [Nat.blt_eq] using h.1

theorem op_rep (hop : PHeCn.opB = true) {j : Nat} (hj : j < 1470) : PHeO.RP j < PHeT.c := by
  unfold PHeCn.opB at hop
  rw [bAnd_iff, bAnd_iff, bAnd_iff] at hop
  have h := allBlk_spec hop.2.2.2 j hj
  have e : Nat.add 0 j = j := Nat.zero_add j
  rw [e] at h
  simpa [Nat.blt_eq] using h

theorem op2_pt (hop2 : PHeCn.opB2 = true) {k b : Nat} (hk : k < 17) (hb : b < 5) :
    powF PHeCn.ziP k b = fld(PHeO.OP, Nat.mul 14 (Nat.mod (Nat.add fld(2636832, Nat.mul 5 b, 31)
      (Nat.sub 17 k)) 17), mask 14) := by
  unfold PHeCn.opB2 at hop2
  have h := allBlk_spec hop2 k hk
  have e : Nat.add 0 k = k := Nat.zero_add k
  rw [e] at h
  have h' := allBlk_spec h b hb
  have e' : Nat.add 0 b = b := Nat.zero_add b
  rw [e'] at h'
  exact Nat.eq_of_beq_eq_true h'

theorem zP_lt (x : Nat) : PHeCn.zP x < 2 ^ 14 := heoFld_lt _ _ _

theorem conj_eq (hO : ∀ g < 3, ∀ r < 8, PHeCn.orbB g r = true) (hop : PHeCn.opB = true)
    (hop2 : PHeCn.opB2 = true) {t : Nat} (ht : t < PHeT.c) (hSG : PHeO.SG t < PHeT.c) :
    E (nfX 5 (PHeCl.XA (PHeO.SG t))) =
      zE ^ (t % 17) * E (nfX 5 (PHeCn.XR (t / 17))) * (zE ^ (t % 17))⁻¹ := by
  have cSzA : PHeT.c = 24990 := Nat.eq_of_beq_eq_true PHeCl.cASz
  have hj : t / 17 < 1470 := by omega
  have hk : t % 17 < 17 := Nat.mod_lt _ (by norm_num)
  have hRP := op_rep hop hj
  have hvA : ∀ i < PHeT.c, nfValidK 5 HeC.LR (nfX 5 (PHeCl.XA i)) = true := fun i hi =>
    (rec_at PHeCl.recA_all hi (by rw [cSzA] at hi; change i < 49 * 8 * 64; omega)).1
  have hkA' : ∀ i < PHeT.c, PHeCl.KA i = keyL 8330 (PHeSn.nfp (nfX 5 (PHeCl.XA i))) PairHe.bs :=
    fun i hi => (rec_at PHeCl.recA_all hi (by rw [cSzA] at hi; change i < 49 * 8 * 64; omega)).2
  have hvR : nfValidK 5 HeC.LR (nfX 5 (PHeCn.XR (t / 17))) = true := hvA _ hRP
  have hrR := E_rep hvR
  have hA := blkAll (G := 3) (R := 8) (B := 64) hO (by norm_num) (by norm_num) (q := t / 17)
    (by omega)
  rw [blt_true hj] at hA
  have hIx : ∀ b ∈ PHeSn.bs, ∀ k < 17, heoIx 17 k fld(2636832, Nat.mul 5 b, mask 5) < 17 :=
    fun b hb k _ => by
      have h := heoIx_lt (L := 17) (t := 1) (k := k) (by norm_num)
        (by rw [Nat.mul_one]; exact op_mb hop (bs_lt hb))
      rwa [Nat.mul_one] at h
  have hs := heoAt_spec (lv := 5) (n := 8330) (L := 17) (N := 17) (mw := 5) (MB := 2636832)
    (OP := PHeO.OP) (bs := PHeSn.bs) (X := PHeCn.XR) (Z := PHeCn.zP) (KS := PHeCn.KS) zP_lt hIx
    (fun m hm => Nat.lt_trans (hrR.lt (op_pt hop hm)) (by norm_num)) hA hk
  have e : Nat.add (Nat.mul (t / 17) 17) (t % 17) = t := Nat.div_add_mod' t 17
  rw [e] at hs
  have hKS : PHeCn.KS t = PHeCl.KA (PHeO.SG t) := rfl
  rw [hKS, hkA' _ hSG, keyL_keyElt (E_rep (hvA _ hSG)) hbs] at hs
  have hg : RepF 8330 (fun b => powF PHeCn.zP (t % 17) (PHeSn.nfp (nfX 5 (PHeCn.XR (t / 17)))
      (powF PHeCn.ziP (t % 17) b))) (zE ^ (t % 17) * E (nfX 5 (PHeCn.XR (t / 17))) *
        ziE ^ (t % 17)) :=
    ((zRep.powF (t % 17)).comp (hrR.comp (ziRep.powF (t % 17)))).congr (by rw [mul_assoc])
  have hk2 : keyL 8330 (fun b => powF PHeCn.zP (t % 17) (nfPtT 14 PHeT.NR PHeT.NR PHeT.LT PHeT.PT 5
      (nfX 5 (PHeCn.XR (t / 17))) fld(PHeO.OP, Nat.mul 14 (heoIx 17 (t % 17)
        fld(2636832, Nat.mul 5 b, mask 5)), mask 14))) PHeSn.bs =
      keyElt 8330 PairHe.bs (zE ^ (t % 17) * E (nfX 5 (PHeCn.XR (t / 17))) * ziE ^ (t % 17)) := by
    rw [← keyL_keyElt hg hbs]
    refine keyL_congr' 8330 fun b hb => ?_
    rw [op2_pt hop2 hk (bs_lt hb), heoIx_one (op_mb hop (bs_lt hb))]
    rfl
  rw [hk2] at hs
  have hmem : zE ^ (t % 17) * E (nfX 5 (PHeCn.XR (t / 17))) * ziE ^ (t % 17) ∈ P3 :=
    P3.mul_mem (P3.mul_mem (P3.pow_mem zMem _) (E_mem hvR)) (P3.pow_mem ziMem _)
  rw [keyElt_inj hH hbs (E_mem (hvA _ hSG)) hmem hs, ziE_eq, inv_pow]

theorem perm_facts (hP : ∀ g < 7, ∀ r < 7, PHeCn.permB g r = true) {t : Nat} (ht : t < PHeT.c) :
    PHeO.SG t < PHeT.c ∧ PHeO.TU (PHeO.SG t) = t := by
  have cSzA : PHeT.c = 24990 := Nat.eq_of_beq_eq_true PHeCl.cASz
  have h := blkAll (G := 7) (R := 7) (B := 512) hP (by norm_num) (by norm_num) (q := t)
    (by rw [cSzA] at ht; omega)
  rw [blt_true ht] at h
  have h' : bAnd(Nat.blt (PHeO.SG t) PHeT.c, Nat.beq (PHeO.TU (PHeO.SG t)) t) = true := h
  rw [bAnd_iff] at h'
  exact ⟨by simpa [Nat.blt_eq] using h'.1, Nat.eq_of_beq_eq_true h'.2⟩

theorem testG_conj (a g j : Equiv.Perm (Fin 8330)) (hc : a * j = j * a) :
    TestG (a * g * a⁻¹) j ↔ TestG g j := by
  have key : ∀ (φ : Equiv.Perm (Fin 8330) ≃* Equiv.Perm (Fin 8330)) (g j : Equiv.Perm (Fin 8330)),
      TestG (φ g) (φ j) ↔ TestG g j := by
    intro φ g j
    simp only [TestG, ← map_mul, ← map_inv, MulEquiv.orderOf_eq]
  have hj : MulAut.conj a j = j := by
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact hc
  have := key (MulAut.conj a) g j
  rwa [hj, MulAut.conj_apply] at this

theorem orb_card (hO : ∀ g < 3, ∀ r < 8, PHeCn.orbB g r = true)
    (hP : ∀ g < 7, ∀ r < 7, PHeCn.permB g r = true) (hop : PHeCn.opB = true)
    (hop2 : PHeCn.opB2 = true) {j : P3} (hj : orderOf j = 17)
    (hc : zE * (j : Equiv.Perm (Fin 8330)) = (j : Equiv.Perm (Fin 8330)) * zE) {J JI : Nat → Nat}
    (hJ : RepF 8330 J (j : Equiv.Perm (Fin 8330))) (hJI : RepF 8330 JI (j : Equiv.Perm (Fin 8330))⁻¹)
    {D1 D0 p : Nat} (hp : p < 8330)
    (hK1 : ∀ i < PHeT.c, Nat.mod (Nat.div (PHeCl.KA i) D1) 8330 =
      PHeSn.nfp (nfX 5 (PHeCl.XA i)) (J p))
    (hK0 : ∀ i < PHeT.c, Nat.mod (Nat.div (PHeCl.KA i) D0) 8330 = PHeSn.nfp (nfX 5 (PHeCl.XA i)) p)
    (hsc : Nat.beq (sumN 3 (fun q => PHeCn.scAt PHeCn.XR PHeCn.KR (nat_lit 1470) J JI D1 D0 q)) 1 =
      true) :
    Nat.card {x : P3 // IsConj tAK x ∧ Qr x (x⁻¹ * j)} = 17 := by
  classical
  have cSzA : PHeT.c = 24990 := Nat.eq_of_beq_eq_true PHeCl.cASz
  have hkA := (ClTP.closNFT_proved (bs := PairHe.bs) (rep := PairHe.wA) He2112.binds He2112.perm
    HeC.ho (by decide) PHeCheck.tabs rfl PHeCheck.hg PHeCheck.repA_eq PHeCheck.okA).2.2
  have hnd := List.nodup_append.1 keys_nodup
  have hndA : ((List.range PHeT.c).map PHeCl.KA).Nodup := by
    rw [← hkA]
    exact hnd.1
  have hvA : ∀ i < PHeT.c, nfValidK 5 HeC.LR (nfX 5 (PHeCl.XA i)) = true := fun i hi =>
    (rec_at PHeCl.recA_all hi (by rw [cSzA] at hi; change i < 49 * 8 * 64; omega)).1
  have clA := card_class_filter (nB := 49) repW_hewA tAMem okA sizeA (cSzA ▸ hkA) (cSzA ▸ hndA)
    PHeCl.recA_all (by norm_num) card_clA
  have hIA : ∀ i < PHeT.c, E (nfX 5 (PHeCl.XA i)) * E (nfX 5 (PHeCl.XA i)) = 1 := fun i hi =>
    class_inv repW_hewA tAMem tAOrd okA sizeA (cSzA ▸ hkA) PHeCl.recA_all (by norm_num)
      (by rw [cSzA] at hi; exact hi)
  rw [card_qr (by rw [Subgroup.orderOf_mk]; exact tAOrd) hj]
  refine (clA (fun p => TestG p (j : Equiv.Perm (Fin 8330)))).trans ?_
  have hc' : ∀ t < 24990, t < PHeT.c := fun t ht => by
    rw [cSzA]
    exact ht
  rw [OrbCount.count_orb (P := fun g => TestG g (j : Equiv.Perm (Fin 8330)))
    (x := fun i => E (nfX 5 (PHeCl.XA i))) (r := fun t => E (nfX 5 (PHeCn.XR t))) (z := zE)
    (n := 1470) (L := 17) (c := 24990) (by norm_num) (by norm_num) PHeO.SG
    (fun t ht => by
      have h := (perm_facts hP (hc' t ht)).1
      rwa [cSzA] at h)
    (fun t ht u hu h => by
      rw [← (perm_facts hP (hc' t ht)).2, ← (perm_facts hP (hc' u hu)).2, h])
    (fun t ht => conj_eq hO hop hop2 (hc' t ht) (perm_facts hP (hc' t ht)).1)
    (fun k g => testG_conj _ g _ ((Commute.pow_left hc k).eq))]
  have hrp : ∀ i < 1470, PHeO.RP i < PHeT.c := fun i hi => op_rep hop hi
  have hs := scan_part (c := nat_lit 1470) (m := 3) (X := PHeCn.XR) (K := PHeCn.KR) j.2 hJ hJI hp
    (fun i hi => hvA _ (hrp i hi)) (fun i hi => hIA _ (hrp i hi))
    (fun i hi => hK1 _ (hrp i hi)) (fun i hi => hK0 _ (hrp i hi))
    (V := fun q => PHeCn.scAt PHeCn.XR PHeCn.KR (nat_lit 1470) J JI D1 D0 q) (fun q _ => rfl)
    (Nat.eq_of_beq_eq_true hsc) (by norm_num)
  rw [hs]

theorem partners_orb (hO : ∀ g < 3, ∀ r < 8, PHeCn.orbB g r = true)
    (hP : ∀ g < 7, ∀ r < 7, PHeCn.permB g r = true) (hR : PHeCn.repB = true)
    (hop : PHeCn.opB = true) (hop2 : PHeCn.opB2 = true) :
    countPair PairHe.bs 7 PairHe.wA PairHe.conds heBlocks ≤ 322560 := by
  classical
  have cSzA : PHeT.c = 24990 := Nat.eq_of_beq_eq_true PHeCl.cASz
  have hvA : ∀ i < PHeT.c, nfValidK 5 HeC.LR (nfX 5 (PHeCl.XA i)) = true := fun i hi =>
    (rec_at PHeCl.recA_all hi (by rw [cSzA] at hi; change i < 49 * 8 * 64; omega)).1
  have hdA := fun i (hi : i < PHeT.c) =>
    key_dig (f := PHeSn.nfp (nfX 5 (PHeCl.XA i))) fun b hb => (E_rep (hvA i hi)).lt (by omega)
  have hkA' : ∀ i < PHeT.c, PHeCl.KA i = keyL 8330 (PHeSn.nfp (nfX 5 (PHeCl.XA i))) PairHe.bs :=
    fun i hi => (rec_at PHeCl.recA_all hi (by rw [cSzA] at hi; change i < 49 * 8 * 64; omega)).2
  have hz0 : PHeCn.zP 0 = 1 := Nat.eq_of_beq_eq_true repsF.2.2.2.2.1
  have hz3 : Nat.beq (PHeCn.z3P 3) 4 = true := by decide
  unfold PHeCn.repB at hR
  rw [bAnd_iff] at hR
  have kA : Nat.card {x : P3 // IsConj tAK x ∧ Qr x (x⁻¹ * zK)} = 17 :=
    orb_card hO hP hop hop2 zK_ord (Commute.refl zE).eq zRep ziRepK (p := 0) (by norm_num)
      (fun i hi => by rw [hz0, hkA' i hi]; exact (hdA i hi).2.1)
      (fun i hi => by rw [hkA' i hi]; exact (hdA i hi).1) hR.1
  have kA3 : Nat.card {x : P3 // IsConj tAK x ∧ Qr x (x⁻¹ * zK ^ 3)} = 17 :=
    orb_card hO hP hop hop2 zK3_ord (by
      rw [SubmonoidClass.coe_pow]
      exact (Commute.self_pow _ 3).eq)
      z3Rep z3iRep (p := 3) (by norm_num)
      (fun i hi => by rw [Nat.eq_of_beq_eq_true hz3, hkA' i hi]; exact (hdA i hi).2.2.2)
      (fun i hi => by rw [hkA' i hi]; exact (hdA i hi).2.2.1) hR.2
  have pA := partners_le tAK kA kA3
  rw [card_clA] at pA
  have hpA : Nat.card {y : P3 // Qr tAK y} ≤ 322560 := by omega
  have hP' : ∀ x : P3, hePartners x = Nat.card {y : P3 // Qr x y} := fun x =>
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      rw [Qr, ← Subgroup.orderOf_coe, patRel_coe])
  rw [← hePartners_rep repW_hewA tAMem]
  exact (hP' tAK).trans_le hpA

end He

end CertificateChecks.KernelSporSch.PHePart

end
