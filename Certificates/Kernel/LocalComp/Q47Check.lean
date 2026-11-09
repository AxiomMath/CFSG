module

public import Certificates.Kernel.LocalComp.Q47Rest
public import Certificates.Kernel.LocalComp.Q47Slices
import CFSG.Certificates.Kernel.Q47KMain
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Q47

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK CFSG.KC.Q47K
open CFSG.ComponentClassification.AS81.Q47 CFSG.ComponentClassification.AS81.HeSylow
open CertificateChecks.KernelLC CertificateChecks.KernelLC.Step44Check

theorem allR_get {f : Nat → Bool} {lo : Nat} : ∀ len, allR f lo len = true →
    ∀ r < len, f (lo + r) = true
  | 0, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | len + 1, h, r, hr => by
    have e : allR f lo (len + 1) = (allR f lo len && f (lo + len)) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge r len with h1 | h1
    · exact allR_get len h.1 r h1
    · have : r = len := by omega
      subst this
      exact h.2

theorem rows {f : Nat → Bool} {k m : Nat} (hk : 0 < k) (h : ∀ b < m, allR f (k * b) k = true) :
    ∀ i < k * m, f i = true := by
  intro i hi
  have hb : i / k < m := (Nat.div_lt_iff_lt_mul hk).2 (by rwa [Nat.mul_comm])
  have := allR_get k (h (i / k) hb) (i % k) (Nat.mod_lt i hk)
  rwa [Nat.div_add_mod] at this

theorem bounds16 : Bound 16 5 q47Rep16 K16.REP ∧
    (heSylZ16 = unpack 16 5 K16.PZ ∧ permOK 16 5 (mask 5) (16 * 5) K16.PZ (pinvS 16 5 (mask 5) K16.PZ) =
      true) ∧
    Bound 64 7 q47D16 K16.GD ∧ Bound 64 7 q47Eb16 K16.GEb ∧ Bound 64 7 q47Fb16 K16.GFb ∧
    (∀ i < 4, Bound 64 7 (kListG q47M16 i) (K16.GK i)) ∧ Bound 64 7 q47C16 K16.CP := by
  have h := kB16
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨bound_of_bndK h1, ⟨bindA_eq (by rw [Bool.and_eq_true]; exact h2), h3⟩, bound_of_bndK h4,
    bound_of_bndK h5, bound_of_bndK h6, fun i hi => bound_of_bndK (allN_spec h7 i hi),
    bound_of_bndK h8⟩

theorem bounds32 : Bound 32 6 q47Rep32 K32.REP ∧
    (heAutZ32 = unpack 32 6 K32.PZ ∧ permOK 32 6 (mask 6) (32 * 6) K32.PZ (pinvS 32 6 (mask 6) K32.PZ) =
      true) ∧
    Bound 64 7 q47D32 K32.GD ∧ Bound 64 7 q47Eb32 K32.GEb ∧ Bound 64 7 q47Fb32 K32.GFb ∧
    (∀ i < 4, Bound 64 7 (kListG q47M32 i) (K32.GK i)) ∧ Bound 64 7 q47C32 K32.CP := by
  have h := kB32
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨bound_of_bndK h1, ⟨bindA_eq (by rw [Bool.and_eq_true]; exact h2), h3⟩, bound_of_bndK h4,
    bound_of_bndK h5, bound_of_bndK h6, fun i hi => bound_of_bndK (allN_spec h7 i hi),
    bound_of_bndK h8⟩

theorem model16 : ModelOK q47D 16 5 q47M16 K16 Q47Y.G := by
  have kx := HeSylowQECheck.kPerm16
  simp only [Bool.and_eq_true] at kx
  obtain ⟨⟨⟨⟨pX, pQ⟩, pE⟩, pF⟩, -⟩ := kx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := bounds16
  exact ⟨b1, b2, HeSylowQECheck.pin16 HeSylowQECheck.kBindX16 pX HeSylX.ok (by decide),
    HeSylowQECheck.pin16 HeSylowQECheck.kBindQ16 pQ HeSylQ.ok (by decide),
    HeSylowQECheck.pin16 HeSylowQECheck.kBindE16 pE HeSylE.ok (by decide),
    HeSylowQECheck.pin16 HeSylowQECheck.kBindF16 pF HeSylF.ok (by decide),
    HeSylowQECheck.pin16 HeSylowQECheck.kBindX16 pX HeSylX.ok (by decide), rfl,
    b3, b4, b5, b6, b7, kRuns16, kRep16, kImg16, kModel16⟩

theorem model32 : ModelOK q47D 32 6 q47M32 K32 Q47Y.G := by
  have ky := HeAutCheck.kPermG
  simp only [Bool.and_eq_true] at ky
  obtain ⟨⟨⟨⟨pY, pQ⟩, pE⟩, pF⟩, -⟩ := ky
  have kp := kPins
  simp only [Bool.and_eq_true] at kp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, bNE⟩, gNE⟩ := kp
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := bounds32
  exact ⟨b1, b2, HeAutCheck.pinY pY, HeAutCheck.pin HeAutCheck.kBindQ pQ HeAutQ.ok (by decide),
    HeAutCheck.pin HeAutCheck.kBindE pE HeAutE.ok (by decide),
    HeAutCheck.pin HeAutCheck.kBindF pF HeAutF.ok (by decide),
    pinB bNE gNE Q47NE.ok (by decide), rfl,
    b3, b4, b5, b6, b7, kRuns32, kRep32, kImg32, kModel32⟩

theorem CS_eq : CS = CSL := by
  have h1 : clsOf q47M16 K16 false = setTs (clsOf q47M16 K16 false) q47TE16E q47T116E q47T216E :=
    eq_setTs (by quickRfl)
  have h2 : clsOf q47M16 K16 true = setTs (clsOf q47M16 K16 true) q47TE16F q47T116F q47T216F :=
    eq_setTs (by quickRfl)
  have h3 : clsOf q47M32 K32 false = setTs (clsOf q47M32 K32 false) q47TE32E q47T132E q47T232E :=
    eq_setTs (by quickRfl)
  have h4 : clsOf q47M32 K32 true = setTs (clsOf q47M32 K32 true) q47TE32F q47T132F q47T232F :=
    eq_setTs (by quickRfl)
  unfold CS CSL
  rw [← h1, ← h2, ← h3, ← h4]

theorem oBlockF_congr {SZ : Nat → Nat} {TR : Nat → Nat → Nat} {m1 m2 : Nat} {W1 W2 : Array Nat}
    {LM : List Nat} {cs cs' : List Cls}
    (h : ∀ t, (cs.all fun c => clsC c t) = (cs'.all fun c => clsC c t)) (s : Nat) :
    oBlockF SZ TR m1 m2 W1 W2 LM cs s = oBlockF SZ TR m1 m2 W1 W2 LM cs' s := by
  have e : okF47 LM cs = okF47 LM cs' := by
    funext t i1 i2
    unfold okF47
    rw [h t]
  unfold oBlockF oStepF
  rw [e]

theorem addT2_eq {c : Cls} {R : List Nat} {W : List (Nat × Nat × Nat × Nat)}
    (pD : ∀ k < c.gD, PP 64 7 (c.GD k)) (h : conjWK c.gD c.GD R W = true) (t : Nat) :
    clsC (addT2 c (W.map Prod.fst)) t = clsC c t :=
  clsC_addT2 (conjWK_sound pD h) t

theorem CSW_all (t : Nat) : (CSW.all fun c => clsC c t) = (CSL.all fun c => clsC c t) := by
  have b16 := bounds16.2.2.1
  have b32 := bounds32.2.2.1
  unfold CSW CSL
  simp only [List.all_cons, List.all_nil]
  rw [addT2_eq (c := setTs (clsOf q47M16 K16 false) q47TE16E q47T116E q47T216E) (R := q47R16E)
      (fun k hk => PP_bound hsz64 b16 hk) (by quickRfl),
    addT2_eq (c := setTs (clsOf q47M16 K16 true) q47TE16F q47T116F q47T216F) (R := q47R16F)
      (fun k hk => PP_bound hsz64 b16 hk) (by quickRfl),
    addT2_eq (c := setTs (clsOf q47M32 K32 false) q47TE32E q47T132E q47T232E) (R := q47R32E)
      (fun k hk => PP_bound hsz64 b32 hk) (by quickRfl),
    addT2_eq (c := setTs (clsOf q47M32 K32 true) q47TE32F q47T132F q47T232F) (R := q47R32F)
      (fun k hk => PP_bound hsz64 b32 hk) (by quickRfl)]

theorem q47TrLin : ∀ k < 6, ∀ j < SZ k, PP 64 7 (TR k j) ∧ addK (TR k j) = true := by
  intro k hk j hj
  have h := allN_spec kT k hk
  rw [Bool.and_eq_true] at h
  have hl := Nat.eq_of_beq_eq_true h.1
  have ka := kAdd
  simp only [Bool.and_eq_true] at ka
  exact ⟨PP_bound hsz64 (bound_of_bndK h.2) (by rw [hl]; exact hj),
    allN_spec (List.all_eq_true.1 ka.1.1.1 k (List.mem_range.2 hk)) j hj⟩

theorem ob_eq {s : Nat} (hs : s < 35) : ob s = Nat.beq (oBlockF SZ TR (maskOf q47W1) (maskOf q47W2)
    q47W1 q47W2 ((List.range 30).map fun j => maskOf (q47L30.getD j #[])) CS s) (BC s) := by
  have m1 : maskOf q47W1 = q47M1 := Nat.eq_of_beq_eq_true (by quickRfl)
  have m2 : maskOf q47W2 = q47M2 := Nat.eq_of_beq_eq_true (by quickRfl)
  have hL : ((List.range 30).map fun j => maskOf (q47L30.getD j #[])) = q47LM :=
    eq_of_beq (by quickRfl)
  have w1 : ∀ a ∈ q47W1.toList, a < 64 := by decide
  have w2 : ∀ a ∈ q47W2.toList, a < 64 := by decide
  unfold ob
  rw [← oBlockF_mat (TM := q47TM) w1 w2 _ _ q47TrLin (fun _ _ _ _ => rfl) hs,
    oBlockF_congr CSW_all, m1, m2, hL, CS_eq]

theorem q47Check_true : q47Check = true := by
  have hD : q47DirectG q47D q47M16 q47M32 = true := by
    rw [q47DirectG, kDT, kDR, kDM, kDM16, kDM32]
    rfl
  have kb := kBnd
  simp only [Bool.and_eq_true] at kb
  obtain ⟨⟨⟨bU1, bU2⟩, bG1⟩, bG2⟩ := kb
  have kp := kPins
  simp only [Bool.and_eq_true] at kp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨bY, gY⟩, bN⟩, gN⟩, bUY1⟩, gUY1⟩, bUY2⟩, gUY2⟩, -⟩, -⟩ := kp
  rw [q47Check_eq]
  exact q47K_sound (d := q47D) (m16 := q47M16) (m32 := q47M32) (k16 := K16) (k32 := K32)
    (TR := TR) (SZ := SZ) (GY := Q47Y.G) (GN := Q47N.G) (GU1 := PK q47U1Gens 7)
    (GU2 := PK q47U2Gens 7) (GG1 := PK q47G1 7) (GG2 := PK q47G2 7) (MPY := MPY) (MPN := MPN)
    (BC := BC) hD
    (fun k hk => by
      have h := allN_spec kT k hk
      rw [Bool.and_eq_true] at h
      exact ⟨Nat.eq_of_beq_eq_true h.1, bound_of_bndK h.2⟩) rfl (by quickRfl)
    (bound_of_bndK bU1) (bound_of_bndK bU2) (bound_of_bndK bG1) (bound_of_bndK bG2)
    (pinB bY gY Q47Y.ok (by decide)) (pinB bN gN Q47N.ok (by decide))
    (pinB bUY1 gUY1 Q47UY1.ok (by decide)) (pinB bUY2 gUY2 Q47UY2.ok (by decide))
    ⟨rfl, rfl, rfl, rfl⟩
    kRun kMP kRef kWit kHead kGenRowY kGenRowN kAdd
    (fun s hs => by
      have h := obAll s hs
      rw [ob_eq hs] at h
      exact h) kBC model16 model32

end CertificateChecks.KernelLC.Q47

end
