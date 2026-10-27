module

public import Certificates.Kernel.Misc.Tits.PVConds8079
public import Certificates.Kernel.Misc.Tits.PiSift8079
public import Certificates.Kernel.Misc.Tits.PiWalk8079

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJT.PV.B2

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelEvenBN CertificateChecks.KernelMisc.TitsJT
open CertificateChecks.KernelMisc.TitsJT.V (sJ)

theorem cPi : Cn TitsPS.Pi := (permC_spec CertificateChecks.KernelMisc.TitsPi.perm).2.1

theorem cPiI : Cn TitsPS.PiI := (permC_spec CertificateChecks.KernelMisc.TitsPi.perm).2.2

theorem piArr_eq : titsPiArr = unpack 1755 11 TitsPS.Pi :=
  CFSG.KC.TitsPi.cmpL_sound CertificateChecks.KernelMisc.TitsPi.bind

theorem piInv_eq : piInv = unpack 1755 11 TitsPS.PiI := by
  rw [piInv, piArr_eq]
  exact (invEqK_sound (permC_spec CertificateChecks.KernelMisc.TitsPi.perm).1).1

theorem cj_canon {A : Nat} (hA : Cn A) : Cn (TitsPS.cj A) := cmpC (cmpC cPi hA) cPiI

theorem conj_eq {A : Nat} (hA : Cn A) : conjPi (unpack 1755 11 A) = unpack 1755 11 (TitsPS.cj A) := by
  unfold conjPi
  rw [piArr_eq, piInv_eq, cmpU cPi hA, cmpU (cmpC cPi hA) cPiI]
  rfl

theorem sift_of {PS PSI LR TR TRI : Nat → Nat} {kS nb BP : Nat} {S : Array (Array Nat)}
    {base : Array Nat} (hb : Binds 1755 11 PS kS nb BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS nb BP) {X : Nat} (hc : Cn X)
    (h : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) LR TRI BP nb 0 X = true) :
    siftA 1755 (rawLevels 1755 S base) base 0 (unpack 1755 11 X) = true := by
  obtain ⟨-, -, hX, hlt⟩ := canonK_facts hc
  exact siftK_soundR hb hp hl rfl hX (allN_of_forall fun i hi => by rw [Nat.blt_eq]; exact hlt i hi) h

theorem words_all {ws : List (List ℤ)} {k : Nat} {PX : Nat → Nat} {f : Array ℕ → Bool}
    (hlen : ws.length = k)
    (hw : allN k (fun i => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13
      ws[i]! (PX i), canonK 1755 11 (mask 11) (1755 * 11) (PX i))) = true)
    (hf : ∀ i < k, Cn (PX i) → f (unpack 1755 11 (TitsPS.cj (PX i))) = true) :
    (ws.all fun w => f (conjPi (wordArr 1755 titsDerivedArrs w))) = true := by
  rw [List.all_eq_true]
  intro w hw'
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw'
  have hik : i < k := by omega
  obtain ⟨w1, w2⟩ := (bAnd_iff _ _).1 (allN_spec hw i hik)
  have e := (wordEqK_sound derBind permD w1).1
  have e' : wordArr 1755 titsDerivedArrs ws[i] = unpack 1755 11 (PX i) := by
    rw [← getElem!_pos ws i hi]
    exact e
  rw [e', conj_eq w2]
  exact hf i hik w2

theorem bS : (titsSWords.all fun w => siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0
    (conjPi (wordArr 1755 titsDerivedArrs w))) = true :=
  words_all (by decide) wS fun i hi hc =>
    sift_of bindsS permS TitsS.hl (cj_canon hc) (allN_spec TitsPS.sS i hi)

theorem bH : (titsHWords.all fun w => siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0
    (conjPi (wordArr 1755 titsDerivedArrs w))) = true :=
  words_all (by decide) wH fun i hi hc =>
    sift_of bindsH permH TitsH.hl (cj_canon hc) (allN_spec TitsPS.sH i hi)

theorem bN : (titsNWords.all fun w => siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0
    (conjPi (wordArr 1755 titsDerivedArrs w))) = true :=
  words_all (by decide) wN fun i hi hc =>
    sift_of bindsN permN TitsN.hl (cj_canon hc) (allN_spec TitsPS.sN i hi)

theorem bJ : (titsJWords.all fun w => siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0
    (conjPi (wordArr 1755 titsDerivedArrs w))) = true :=
  words_all (by decide) wJ fun i hi hc =>
    sift_of bindsJ permJ TitsJ.hl (cj_canon hc) (allN_spec TitsPS.sJ i hi)

theorem bK : (titsKWords.all fun w => siftA 1755 titsKLevels (baseArr 1755 titsKBase) 0
    (conjPi (wordArr 1755 titsDerivedArrs w))) = true :=
  words_all (by decide) wK fun i hi hc =>
    sift_of bindsK permK TitsK.hl (cj_canon hc) (allN_spec TitsPS.sK i hi)

theorem bSq : siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0
    (compA 1755 titsPiArr titsPiArr) = true := by
  rw [piArr_eq, cmpU cPi cPi]
  exact sift_of bindsJ permJ TitsJ.hl (cmpC cPi cPi) TitsPS.sq

theorem bT : (allLt 3 fun k => siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0
    (compA 1755 (compA 1755 (compA 1755 jGenArrs[k]! titsPiArr) jGenInvArrs[k]!) piInv)) =
    true := by
  refine allLt_iff.2 fun k hk => ?_
  obtain ⟨c1, c2, c3, -⟩ := canK_at (k := k) (by omega)
  rw [genInv_get hk, (hGenArr hk).1, (invEqK_sound c3).1, piArr_eq, piInv_eq, cmpU c1 cPi,
    cmpU (cmpC c1 cPi) c2, cmpU (cmpC (cmpC c1 cPi) c2) cPiI]
  exact sift_of bindsJ permJ TitsJ.hl (cmpC (cmpC (cmpC c1 cPi) c2) cPiI) (allN_spec TitsPS.sT k hk)

theorem piHyp_of
    (hJ : (titsJWords.all fun w => siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0
      (conjPi (wordArr 1755 titsDerivedArrs w))) = true)
    (hS : siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 (compA 1755 titsPiArr titsPiArr) = true)
    (hT : (allLt 3 fun k => siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0
      (compA 1755 (compA 1755 (compA 1755 jGenArrs[k]! titsPiArr) jGenInvArrs[k]!) piInv)) = true) :
    PiHyp where
  conjJ k hk := by
    have hk' : k < titsJWords.length := by simpa [titsJWords] using hk
    have hw : titsJWords[k]! ∈ titsJWords := by
      rw [getElem!_pos titsJWords k hk']
      exact List.getElem_mem _
    have r : Rep 1755 (conjPi (wordArr 1755 titsDerivedArrs titsJWords[k]!)) (piP * sJ k * piP⁻¹) :=
      rep_compA (rep_compA pi_rep (rep_wordArr_titsT (jWords_letters _ hw))) (rep_invCandJ pi_rep)
    exact mem_titsJ_of_sift r (List.all_eq_true.1 hJ _ hw)
  sq := mem_titsJ_of_sift (rep_compA pi_rep pi_rep) hS
  conjH k hk := by
    have r : Rep 1755 (compA 1755 (compA 1755 (compA 1755 jGenArrs[k]! titsPiArr) jGenInvArrs[k]!)
        piInv) (hGen k * piP * (hGen k)⁻¹ * piP⁻¹) := by
      rw [genInv_get hk]
      exact rep_compA (rep_compA (rep_compA (hGenArr hk).2 pi_rep) (rep_invCandJ (hGenArr hk).2))
        (rep_invCandJ pi_rep)
    exact mem_titsJ_of_sift r (allLt_spec hT hk)

theorem hπ : PiHyp := piHyp_of bJ bSq bT

theorem extract_get {j : ℕ} (hj : j < 3) : (titsSArrs.extract 0 3)[j]! = unpack 1755 11 (TitsS.S j) := by
  have hsz : titsSArrs.size = 9 := size_of bindsS
  rw [getElem!_pos _ j (by simp [hsz]; omega), Array.getElem_extract, ← getElem!_pos _ _ (by omega)]
  simp only [Nat.zero_add]
  exact get_of bindsS j (by omega)

theorem cS {j : ℕ} (hj : j < 3) : Cn (TitsS.S j) := ((bAnd_iff _ _).1 (allN_spec wS j hj)).2

theorem bW : all5 1755 titsSLevels (fun a => !(commutesAll 1755 (compA 1755 a titsPiArr)
    (titsSArrs.extract 0 3))) = true := by
  refine all5K_sound bindsS permS TitsS.hl
    (P := TitsPW.ncQ CertificateChecks.KernelMisc.TitsPi.P) ?_ TitsPW.walk
  intro t0 t1 t2 t3 t4 h0 h1 h2 h3 h4 _ hP
  rw [Bool.not_eq_true', Bool.eq_false_iff]
  intro hc
  have ka := (gpt_facts h0 h1 h2 h3 h4).2
  obtain ⟨-, -, -, rp⟩ := canonK_facts cPi
  have hall : allN 3 (fun j => TitsPW.commQ CertificateChecks.KernelMisc.TitsPi.P (TitsS.S j)
      t0 t1 t2 t3 t4) = true := by
    refine allN_of_forall fun j hj => ?_
    obtain ⟨-, -, -, rg⟩ := canonK_facts (cS hj)
    unfold commutesAll at hc
    have hj' : j < (titsSArrs.extract 0 3).size := by simp [size_of bindsS]; omega
    have e := allLt_spec hc hj'
    rw [extract_get hj, piArr_eq] at e
    unfold eqA at e
    refine allN_of_forall fun x hx => ?_
    have hb := beq_iff_eq.1 (allLt_spec e hx)
    rw [compA_get hx, unpack_getT (P := TitsS.S j) hx, compA_get (rg x hx),
      unpack_getT (P := TitsPS.Pi) (rg x hx), (ka _ (rp _ (rg x hx))).1, compA_get hx,
      compA_get hx, unpack_getT (P := TitsPS.Pi) hx, (ka _ (rp _ hx)).1,
      unpack_getT (P := TitsS.S j) (ka _ (rp _ hx)).2] at hb
    rw [Nat.beq_eq]
    exact hb
  unfold TitsPW.ncQ at hP
  rw [hall] at hP
  exact absurd hP (by decide)

theorem bZ : eqA 1755 (compA 1755 (compA 1755 titsPiArr jZArr) piInv) jZArr = true := by
  have rz : Rep 1755 jZArr titsZ := titsZ_rep
  have r : Rep 1755 (compA 1755 (compA 1755 titsPiArr jZArr) piInv) (piP * titsZ * piP⁻¹) :=
    rep_compA (rep_compA pi_rep rz) (rep_invCandJ pi_rep)
  refine (eqA_iff r rz).2 ?_
  rw [← (z_pi hπ).eq, mul_inv_cancel_right]

theorem bFix : (allLt 512 fun i => !(titsJBase.all fun p => (jPel[i]!)[titsPiArr[p]!]! == p)) =
    true := by
  refine allLt_iff.2 fun i hi => ?_
  have h : (titsJBase.all fun p => (jPel[i]!)[titsPiArr[p]!]! == p) = false := by
    rw [Bool.eq_false_iff]
    intro h
    refine noFix (el_mem hi) fun p hp => ?_
    have hp' := base_lt hp
    have e := beq_iff_eq.1 (List.all_eq_true.1 h p hp)
    rw [rep_base pi_rep p hp', (el_rep hi) (piP (finPt 1755 p))] at e
    rw [Equiv.Perm.mul_apply]
    exact e
  rw [h]
  rfl

theorem batch2 :
    isInvA 1755 titsPiArr piInv = true ∧
    (titsSWords.all fun w => siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0
      (conjPi (wordArr 1755 titsDerivedArrs w))) = true ∧
    (titsHWords.all fun w => siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0
      (conjPi (wordArr 1755 titsDerivedArrs w))) = true ∧
    (titsNWords.all fun w => siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0
      (conjPi (wordArr 1755 titsDerivedArrs w))) = true ∧
    (titsJWords.all fun w => siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0
      (conjPi (wordArr 1755 titsDerivedArrs w))) = true ∧
    (titsKWords.all fun w => siftA 1755 titsKLevels (baseArr 1755 titsKBase) 0
      (conjPi (wordArr 1755 titsDerivedArrs w))) = true ∧
    siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 (compA 1755 titsPiArr titsPiArr) = true ∧
    (allLt 3 fun k => siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0
      (compA 1755 (compA 1755 (compA 1755 jGenArrs[k]! titsPiArr) jGenInvArrs[k]!) piInv)) = true ∧
    all5 1755 titsSLevels (fun a => !(commutesAll 1755 (compA 1755 a titsPiArr)
      (titsSArrs.extract 0 3))) = true ∧
    eqA 1755 (compA 1755 (compA 1755 titsPiArr jZArr) piInv) jZArr = true ∧
    (allLt 512 fun i => !(titsJBase.all fun p => (jPel[i]!)[titsPiArr[p]!]! == p)) = true :=
  ⟨isInvA_invCand pi_rep, bS, bH, bN, bJ, bK, bSq, bT, bW, bZ, bFix⟩

end CertificateChecks.KernelMisc.TitsJT.PV.B2

end
