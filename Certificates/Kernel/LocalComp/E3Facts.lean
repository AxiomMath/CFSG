
module

public import Certificates.Kernel.LocalComp.E3Blocks
public import Certificates.Kernel.LocalComp.E3BlocksL2
public import Certificates.Kernel.LocalComp.E3BlocksL3
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentRigidCheckInputs
import CFSG.Certificates.Kernel.E3SoundProof
import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Co3Id

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.KC.Co3Bfs CFSG.KC.E3
open CFSG.KC.Child3 (offOK)
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.Schreier.Co3.Native CertificateChecks.KernelLC CertificateChecks.KernelSpor

theorem dd_all (j : Nat) (hj : j < 4608) : ddK j = true :=
  cover_of_blocks (B := 4608) (nb := 1) (by omega) (Nat.le_of_eq rfl) BD.all j hj
theorem l1_all (j : Nat) (hj : j < 4608) : l1K j = true :=
  cover_of_blocks (B := 128) (nb := 36) (by omega) (Nat.le_of_eq rfl) B1.all j hj
theorem pos_all (p : Nat) (hp : p < 576) : cdPos p = true :=
  cover_of_blocks (B := 64) (nb := 9) (by omega) (Nat.le_of_eq rfl) BP.all p hp
theorem mem_all' (j : Nat) (hj : j < 4608) : cdMem j = true :=
  cover_of_blocks (B := 1152) (nb := 4) (by omega) (Nat.le_of_eq rfl) BM.all j hj
theorem leafH_all (ℓ : Nat) (hl : ℓ < 16) : leafH ℓ = true :=
  cover_of_blocks (B := 1) (nb := 16) (by omega) (Nat.le_of_eq rfl) BH.all ℓ hl
theorem leafC_all (y : Nat) (hy : y < 2048) : leafC y = true :=
  cover_of_blocks (B := 16) (nb := 128) (by omega) (Nat.le_of_eq rfl) BC.all y hy
theorem l2_all (x : Nat) (hx : x < 13824) : l2K x = true :=
  cover_of_blocks (B := 96) (nb := 144) (by omega) (Nat.le_of_eq rfl) B2.all x hx
theorem l3_all (x : Nat) (hx : x < 36864) : l3K x = true :=
  cover_of_blocks (B := 96) (nb := 384) (by omega) (Nat.le_of_eq rfl) B3.all x hx

theorem hIdx_E (k : Nat) (hk : k < 4608) : hIdx (unpack 276 9 (HR.E k)) = k := by
  have h := bfsR_pos g_eq (fun i hi => allN_spec kGc i hi) (by rw [hc]; omega) (by rw [hc])
    (Nat.eq_of_beq_eq_true kRootE) (Nat.eq_of_beq_eq_true kRootP) (Nat.eq_of_beq_eq_true kRootL)
    (fun k hk => (hAll_spec k hk).1) (fun k h0 hk => (hAll_spec k hk).2.1 h0)
    (fun k h0 hk => (hAll_spec k (by omega)).2.2.1 h0 hk) (fun m hm => (hAll_spec m hm).2.2.2.1)
    (fun q hq i hi => (hAll_spec q hq).2.2.2.2 i hi) k (by rw [hc]; exact hk)
  unfold hIdx hPos hKey
  rw [keyOf_unpack2, ← hBFS_eq] at *
  rw [h]
  rfl

theorem hIdx_of {X : Nat} {k : Nat} (hk : k < 4608) (h : Nat.beq (HR.E k) X = true) :
    hIdx (unpack 276 9 X) = k := by
  rw [← Nat.eq_of_beq_eq_true h]
  exact hIdx_E k hk

theorem kGI : allN 3 (fun i => bAnd(invEqK 276 9 (mask 9) (276 * 9) (HR.G i) (GI i),
    canonK 276 9 (mask 9) (276 * 9) (GI i))) = true := by quickRfl

theorem gi_eq (i : Nat) (hi : i < 3) : invCand 276 gArrs[i]! = unpack 276 9 (GI i) := by
  rw [g_eq i hi]
  exact (invEqK_sound ((bAnd_iff _ _).1 (allN_spec kGI i hi)).1).1

theorem cGI (i : Nat) (hi : i < 3) : Cn (GI i) := ((bAnd_iff _ _).1 (allN_spec kGI i hi)).2

@[expose] noncomputable def GPs : List Nat := [HR.G 0, HR.G 1, HR.G 2]

theorem gps_eq (i : Nat) (hi : i < 3) : gArrs[i]! = unpack 276 9 (lget GPs i) := by
  rw [g_eq i hi]
  interval_cases i <;> rfl

theorem gps_c (i : Nat) (hi : i < 3) : Cn (lget GPs i) := by
  have := cG i hi
  interval_cases i <;> exact this

theorem ws_eq {k L : Nat} (hk : k ≤ 3) :
    withProf (testWords k L) = (testWords k L).map fun w =>
      (w, (List.range 24).map fun m => swapZ (zcK P0 P4 EAP (powR (prodP GPs w) (m + 1)))) := by
  unfold withProf
  refine List.map_congr_left fun w hw => ?_
  have hl := mem_testWords hw
  obtain ⟨e, c⟩ := prodA_unpack (k := 3) gps_eq gps_c w fun i hi => by have := hl i hi; omega
  rw [e, expProf_unpack c]

theorem ws1 : wsE1 = E3.WS1 := by
  unfold wsE1
  rw [ws_eq (by omega)]
  decide +kernel

theorem ws2 : wsE2 = E3.WS2 := by
  unfold wsE2
  rw [ws_eq (by omega)]
  decide +kernel

theorem ws3 : wsE3 = E3.WS3 := by
  unfold wsE3
  rw [ws_eq (by omega)]
  decide +kernel

theorem ws_letters {k L : Nat} : ∀ p ∈ withProf (testWords k L), ∀ i ∈ p.1, i < k := by
  intro p hp i hi
  unfold withProf at hp
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hp
  exact mem_testWords hw i hi

theorem tests1 (j : Nat) (hj : j < 4608) :
    testsOK #[hList[j]!] wsE1 = testK P0 P4 EAP [HR.E j] E3.WS1 := by
  rw [testsOK_unpack (k := 1) (Ys := [HR.E j]) (fun i hi => by
      interval_cases i
      exact hList_get j hj) (fun i hi => by interval_cases i; exact cHR j hj)
    (ws := wsE1) (by unfold wsE1; exact ws_letters), ws1]

theorem tests2 (r j : Nat) (hr : r < 4608) (hj : j < 4608) :
    testsOK #[hList[r]!, hList[j]!] wsE2 = testK P0 P4 EAP [HR.E r, HR.E j] E3.WS2 := by
  rw [testsOK_unpack (k := 2) (Ys := [HR.E r, HR.E j]) (fun i hi => by
      interval_cases i
      · exact hList_get r hr
      · exact hList_get j hj) (fun i hi => by
      interval_cases i
      · exact cHR r hr
      · exact cHR j hj) (ws := wsE2) (by unfold wsE2; exact ws_letters), ws2]

theorem tests3 (r j₂ j₃ : Nat) (hr : r < 4608) (h2 : j₂ < 4608) (h3 : j₃ < 4608) :
    testsOK #[hList[r]!, hList[j₂]!, hList[j₃]!] wsE3 =
      testK P0 P4 EAP [HR.E r, HR.E j₂, HR.E j₃] E3.WS3 := by
  rw [testsOK_unpack (k := 3) (Ys := [HR.E r, HR.E j₂, HR.E j₃]) (fun i hi => by
      interval_cases i
      · exact hList_get r hr
      · exact hList_get j₂ h2
      · exact hList_get j₃ h3) (fun i hi => by
      interval_cases i
      · exact cHR r hr
      · exact cHR j₂ h2
      · exact cHR j₃ h3) (ws := wsE3) (by unfold wsE3; exact ws_letters), ws3]

theorem tst_eq (j : Nat) (hj : j < 4608) :
    testsOK #[hList[j]!] wsE1 = (E3.TB j == 1) := by
  rw [tests1 j hj]
  have h := l1_all j hj
  unfold l1K at h
  cases hb : Nat.beq (E3.TB j) 1
  · rw [hb] at h
    rw [testK_false h]
    have : (E3.TB j == 1) = false := by
      rw [Bool.eq_false_iff]
      intro h'
      rw [beq_iff_eq] at h'
      rw [h', Nat.beq_refl] at hb
      exact Bool.noConfusion hb
    rw [this]
  · rw [hb] at h
    rw [((bAnd_iff _ _).1 h).1]
    have : (E3.TB j == 1) = true := by
      rw [beq_iff_eq]
      exact Nat.eq_of_beq_eq_true hb
    rw [this]

theorem kOff : offOK E3.CS E3.OFF E3.N = true := by quickRfl

theorem kCS : allN E3.CS.length (fun c => Nat.blt 0 (lget E3.CS c)) = true := by quickRfl

theorem kMI : allN 4608 (fun j => bIf(Nat.blt (E3.MI j) E3.N, Nat.beq (E3.M (E3.MI j)) j, true)) =
    true := by quickRfl

theorem hN : E3.N = 576 := rfl

theorem hRL : (List.range E3.CS.length).map (fun c => E3.M (lget E3.OFF c)) = E3.R := by
  decide +kernel

theorem classData_eq : classData = (E3.R.toArray,
    Array.ofFn (n := 4608) (fun j => ckF E3.CI E3.MI E3.N j.val),
    Array.ofFn (n := 4608) (fun j => ciF E3.CS E3.OFF E3.CI E3.CV E3.MI E3.N j.val)) := by
  have e : classData = classDataG hList gArrs hIdx (fun t => testsOK #[t] wsE1) := rfl
  rw [e, ← hRL]
  exact classData_rec (E := HR.E) (GP := HR.G) (GIP := GI) (TB := E3.TB) hList_get
    (fun i hi => ⟨g_eq i hi, gi_eq i hi⟩) (fun i hi => ⟨cG i hi, cGI i hi⟩) hIdx_E
    (fun k hk => cHR k hk) tst_eq kOff kCS kMI (fun p hp => pos_all p (by rw [hN] at hp; exact hp))
    mem_all'

theorem kIdx : (E3.R.all fun r => decide (r < 4608)) ∧ E3.R.length = 3 ∧ E3.P2.length = 8 ∧
    E3.P3.length = 16 ∧ (E3.P3.all fun x => decide (x / 4608 < 8)) := by decide +kernel

theorem R_lt (k : Nat) (hk : k < 3) : lget E3.R k < 4608 := by
  interval_cases k <;> decide

theorem lget_toArray (l : List Nat) (i : Nat) : l.toArray[i]! = lget l i := by
  rw [lget_eq]
  simp [getElem!_def, List.getD_eq_getElem?_getD]
  cases l[i]? <;> rfl

theorem anyLt_of {n : Nat} {p : Nat → Bool} {i : Nat} (hi : i < n) (h : p i = true) :
    CFSG.EvenSmallLie.SympSix.Co3Ident.anyLt n p = true := by
  unfold CFSG.EvenSmallLie.SympSix.Co3Ident.anyLt
  exact List.any_eq_true.2 ⟨i, List.mem_range.2 hi, h⟩

theorem lget_idxOf {l : List Nat} {x : Nat} (h : l.contains x = true) :
    l.idxOf x < l.length ∧ lget l (l.idxOf x) = x := by
  have hm : x ∈ l := List.contains_iff_mem.1 h
  have hlt := List.idxOf_lt_length_iff.2 hm
  refine ⟨hlt, ?_⟩
  rw [lget_eq, List.getD_eq_getElem _ _ hlt, List.getElem_idxOf hlt]

@[expose] noncomputable def leafI (ℓ : Nat) : List Nat :=
  [lget E3.R (lget E3.P2 (lget E3.P3 ℓ / 4608) / 4608), lget E3.P2 (lget E3.P3 ℓ / 4608) % 4608,
    lget E3.P3 ℓ % 4608]

theorem kLeafI : ∀ ℓ < 16, (leafI ℓ).all fun i => decide (i < 4608) := by decide +kernel

theorem leafI_lt (ℓ : Nat) (hl : ℓ < 16) (m : Nat) (hm : m < 3) : lget (leafI ℓ) m < 4608 := by
  have h := List.all_eq_true.1 (kLeafI ℓ hl) (lget (leafI ℓ) m) (by
    rw [lget_eq, List.getD_eq_getElem _ _ (by simp [leafI]; omega)]
    exact List.getElem_mem _)
  simpa using h

theorem leafY_eq (ℓ m : Nat) (hm : m < 3) : lget (leafY ℓ) m = HR.E (lget (leafI ℓ) m) := by
  interval_cases m <;> rfl

theorem cY' (ℓ : Nat) (hl : ℓ < 16) (m : Nat) (hm : m < 3) : Cn (lget (leafY ℓ) m) := by
  rw [leafY_eq ℓ m hm]
  exact cHR _ (leafI_lt ℓ hl m hm)

@[expose] noncomputable def leafA (ℓ : Nat) : Array (Array Nat) :=
  #[unpack 276 9 (lget (leafY ℓ) 0), unpack 276 9 (lget (leafY ℓ) 1), unpack 276 9 (lget (leafY ℓ) 2)]

theorem leafA_get (ℓ m : Nat) (hm : m < 3) : (leafA ℓ)[m]! = unpack 276 9 (lget (leafY ℓ) m) := by
  interval_cases m <;> rfl

theorem psi_eq (m : Nat) (hm : m < 3) : psiGArrs[m]! = unpack 276 9 (PSI m) := by
  rw [psiGArrs_getElem hm, bind3, g_eq m hm, compA_unpack (cG m hm) c3,
    compA_unpack c3 (canon_pc (cG m hm) c3)]
  rfl

theorem cPSI (m : Nat) (hm : m < 3) : Cn (PSI m) := canon_pc c3 (canon_pc (cG m hm) c3)

theorem psi_ok (ℓ : Nat) (hl : ℓ < 16) {i : Nat} (hi : i < 4608)
    (h : allN 3 (fun m => Nat.beq (pc (HR.E i) (PSI m)) (pc (lget (leafY ℓ) m) (HR.E i))) = true) :
    psiFormOK (leafA ℓ) = true := by
  unfold psiFormOK
  refine anyLt_of hi ?_
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro m hm
  rw [hList_get i hi, psi_eq m hm, leafA_get ℓ m hm, compA_unpack (cHR i hi) (cPSI m hm),
    compA_unpack (cY' ℓ hl m hm) (cHR i hi),
    eqA_unpack (canon_pc (cHR i hi) (cPSI m hm)) (canon_pc (cY' ℓ hl m hm) (cHR i hi))]
  exact allN_spec h m hm

theorem step_PL (j : Nat) (hj : j < 4608) (h0 : 0 < j) : HR.P j < j ∧ HR.L j < 3 := by
  have h := (hAll_spec j (by rw [hc]; exact hj)).2.1 h0
  unfold stepR at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, _⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2⟩

theorem treeP_canon {Ys : List Nat} (hY : ∀ m < 3, Cn (lget Ys m)) :
    ∀ f j, j < 4608 → Cn (treeP HR.P HR.L (lget Ys) f j) := by
  intro f
  induction f with
  | zero => intro j _; exact kCid
  | succ f ih =>
    intro j hj
    unfold treeP
    cases hb : Nat.beq j 0
    · have h0 : 0 < j := Nat.pos_of_ne_zero (Nat.ne_of_beq_eq_false hb)
      obtain ⟨hp, hl⟩ := step_PL j hj h0
      exact canon_pc (ih _ (by omega)) (hY _ hl)
    · exact kCid

theorem dd_spec (j : Nat) (hj : j < 4608) (h0 : 0 < j) : E3.DD j = E3.DD (HR.P j) + 1 := by
  have h := dd_all j hj
  unfold ddK at h
  rw [beq_zero_false h0] at h
  exact Nat.eq_of_beq_eq_true h

theorem dd0 : E3.DD 0 = 0 := by
  have h := dd_all 0 (by omega)
  unfold ddK at h
  exact Nat.eq_of_beq_eq_true h

theorem sigma_eq (ℓ : Nat) (hl : ℓ < 16) :
    sigmaTab (leafA ℓ) = Array.ofFn (n := 4608) (fun j => unpack 276 9 (TPl ℓ j.val)) := by
  have e : sigmaTab (leafA ℓ) = sigmaTabG hPar hLab (leafA ℓ) := rfl
  rw [e]
  exact sigmaTab_tree hPar_get hLab_get (leafA_get ℓ) (cY' ℓ hl) dd0
    fun j h0 hj => ⟨(step_PL j hj h0).1, (step_PL j hj h0).2, dd_spec j hj h0⟩

theorem TPl_get (ℓ : Nat) (hl : ℓ < 16) (i : Nat) (hi : i < 4608) :
    (sigmaTab (leafA ℓ))[i]! = unpack 276 9 (TPl ℓ i) := by
  rw [sigma_eq ℓ hl]
  exact ofFn_get (fun j => unpack 276 9 (TPl ℓ j)) hi

theorem cTPl (ℓ : Nat) (hl : ℓ < 16) (i : Nat) (hi : i < 4608) : Cn (TPl ℓ i) :=
  treeP_canon (cY' ℓ hl) _ i hi

theorem treeP_succ (PP LL YP : Nat → Nat) (f j : Nat) :
    treeP PP LL YP (f + 1) j = nIf(Nat.beq j 0, pidn 276 9, pc (treeP PP LL YP f (PP j)) (YP (LL j))) :=
  rfl

theorem TPl_step (ℓ j : Nat) (hj : j < 4608) (h0 : 0 < j) :
    TPl ℓ j = pc (TPl ℓ (HR.P j)) (lget (leafY ℓ) (HR.L j)) := by
  unfold TPl
  rw [dd_spec j hj h0, treeP_succ, beq_zero_false h0]

theorem eqA_self' (t : Array Nat) : eqA 276 t t = true := by
  unfold eqA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem treeTab_leaf (ℓ : Nat) (hl : ℓ < 16) :
    treeTabOK 276 (leafA ℓ) hPar hLab (sigmaTab (leafA ℓ)) 4608 = true := by
  unfold treeTabOK
  rw [Bool.and_eq_true, CFSG.Monster.B.Co2.allLt_iff]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [TPl_get ℓ hl 0 (by omega)]
    have : TPl ℓ 0 = pidn 276 9 := by
      unfold TPl
      rw [dd0]
      rfl
    rw [this, idK_sound kId]
    exact eqA_self' _
  · rcases Nat.eq_zero_or_pos j with rfl | h0
    · rfl
    · obtain ⟨hp, hlb⟩ := step_PL j hj h0
      rw [hPar_get j hj, hLab_get j hj, TPl_get ℓ hl j hj, TPl_get ℓ hl _ (by omega),
        leafA_get ℓ _ hlb, compA_unpack (cTPl ℓ hl _ (by omega)) (cY' ℓ hl _ hlb),
        ← TPl_step ℓ j hj h0]
      have hs : (leafA ℓ).size = 3 := rfl
      simp [hp, hlb, hs, eqA_self']

theorem comp3 {A B C : Nat} (hA : Cn A) (hB : Cn B) (hC : Cn C) :
    compA 276 (unpack 276 9 A) (compA 276 (unpack 276 9 B) (unpack 276 9 C)) =
      unpack 276 9 (pc A (pc B C)) := by
  rw [compA_unpack hB hC, compA_unpack hA (canon_pc hB hC)]

theorem kHI : allN 16 (fun ℓ => canonK 276 9 (mask 9) (276 * 9)
    (pinvS 276 9 (mask 9) (HR.E (lget E3.LI ℓ)))) = true := by quickRfl

theorem beq_false_of {b : Bool} (h : Bool.rec (motive := fun _ => Bool) true false b = true) :
    b = false := by
  cases b
  · rfl
  · exact Bool.noConfusion h

theorem chain_ok (ℓ : Nat) (hl : ℓ < 16) (hLK : Nat.beq (lget E3.LK ℓ) 0 = false)
    (hi : lget E3.LI ℓ < 4608)
    (hHI : invCand 276 (unpack 276 9 (HR.E (lget E3.LI ℓ))) =
      unpack 276 9 (pinvS 276 9 (mask 9) (HR.E (lget E3.LI ℓ))))
    (k : Nat) (hk : k < 4608) (hck : commutesA 276 hList[k]! yArr = true) :
    CFSG.EvenSmallLie.SympSix.Co3Ident.anyLt 4608 (fun j₀ => commutesA 276 hList[j₀]! yArr &&
      chainBad (sigmaTab (leafA ℓ)) (unpack 276 9 (HR.E (lget E3.LI ℓ)))
        (unpack 276 9 (pinvS 276 9 (mask 9) (HR.E (lget E3.LI ℓ)))) j₀ k) = true := by
  have cH := cHR _ hi
  have cHI : Cn (pinvS 276 9 (mask 9) (HR.E (lget E3.LI ℓ))) := allN_spec kHI ℓ hl
  rw [hcomm k hk, mem_all k hk] at hck
  obtain ⟨hcl, hck'⟩ := lget_idxOf hck
  rw [CL_length] at hcl
  have hy : 128 * ℓ + CL.idxOf k < 2048 := by omega
  have hC := leafC_all _ hy
  unfold leafC at hC
  simp only [CFSG.KC.Fendel.strictB_eq] at hC
  have e1 : (128 * ℓ + CL.idxOf k) / 128 = ℓ := by omega
  have e2 : (128 * ℓ + CL.idxOf k) % 128 = CL.idxOf k := by omega
  rw [e1, e2, hLK, hck'] at hC
  dsimp only at hC
  generalize hY : 128 * ℓ + CL.idxOf k = y at hC
  generalize E3.LW (Nat.add (Nat.mul 6 y) 0) = j0 at hC
  generalize E3.LW (Nat.add (Nat.mul 6 y) 1) = w1 at hC
  generalize E3.LW (Nat.add (Nat.mul 6 y) 2) = w1' at hC
  generalize E3.LW (Nat.add (Nat.mul 6 y) 3) = w2 at hC
  generalize E3.LW (Nat.add (Nat.mul 6 y) 4) = w2' at hC
  generalize E3.LW (Nat.add (Nat.mul 6 y) 5) = w3 at hC
  generalize HR.E (lget E3.LI ℓ) = H at hC cH cHI hHI ⊢
  obtain ⟨hj0, hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨hw1, hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨hw1', hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨hw2, hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨hw2', hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨hw3, hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨hcy, hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨b1, hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨b1', hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨b2, hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨b2', hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨b3, hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨c1, hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨c2, hC⟩ := (bAnd_iff _ _).1 hC
  obtain ⟨c3, hfin⟩ := (bAnd_iff _ _).1 hC
  have hfin' := beq_false_of hfin
  have hj0' : j0 < 4608 := Nat.le_of_ble_eq_true hj0
  have hw1l : w1 < 4608 := Nat.le_of_ble_eq_true hw1
  have hw1'l : w1' < 4608 := Nat.le_of_ble_eq_true hw1'
  have hw2l : w2 < 4608 := Nat.le_of_ble_eq_true hw2
  have hw2'l : w2' < 4608 := Nat.le_of_ble_eq_true hw2'
  have hw3l : w3 < 4608 := Nat.le_of_ble_eq_true hw3
  refine anyLt_of hj0' ?_
  rw [hcomm j0 hj0', hcy, Bool.true_and]
  unfold chainBad
  dsimp +zetaHave only
  rw [hList_get j0 hj0', comp3 cH (cHR j0 hj0') cHI, hIdx_of hw1l b1, TPl_get ℓ hl w1 hw1l, bcb_eq,
    comp3 cBCB (cTPl ℓ hl w1 hw1l) cBCB, hIdx_of hw1'l b1', hList_get w1' hw1'l,
    comp3 cH (cHR w1' hw1'l) cHI, hIdx_of hw2l b2, TPl_get ℓ hl w2 hw2l,
    comp3 cBCB (cTPl ℓ hl w2 hw2l) cBCB, hIdx_of hw2'l b2', hList_get w2' hw2'l,
    comp3 cH (cHR w2' hw2'l) cHI, hIdx_of hw3l b3, TPl_get ℓ hl w3 hw3l,
    comp3 cBCB (cTPl ℓ hl w3 hw3l) cBCB, hList_get w1 hw1l, hList_get w2 hw2l,
    hList_get w3 hw3l, hList_get k hk,
    compA_unpack (cHR w1 hw1l) cH, compA_unpack cH (cHR j0 hj0'),
    compA_unpack (cHR w2 hw2l) cH, compA_unpack cH (cHR w1' hw1'l),
    compA_unpack (cHR w3 hw3l) cH, compA_unpack cH (cHR w2' hw2'l),
    compA_unpack (canon_pc cBCB (canon_pc (cTPl ℓ hl w3 hw3l) cBCB)) (cHR k hk),
    compA_unpack (cHR k hk) (cHR j0 hj0'),
    eqA_unpack (canon_pc (cHR w1 hw1l) cH) (canon_pc cH (cHR j0 hj0')),
    eqA_unpack (cHR w1' hw1'l) (canon_pc cBCB (canon_pc (cTPl ℓ hl w1 hw1l) cBCB)),
    eqA_unpack (canon_pc (cHR w2 hw2l) cH) (canon_pc cH (cHR w1' hw1'l)),
    eqA_unpack (cHR w2' hw2'l) (canon_pc cBCB (canon_pc (cTPl ℓ hl w2 hw2l) cBCB)),
    eqA_unpack (canon_pc (cHR w3 hw3l) cH) (canon_pc cH (cHR w2' hw2'l)),
    eqA_unpack (canon_pc (canon_pc cBCB (canon_pc (cTPl ℓ hl w3 hw3l) cBCB)) (cHR k hk))
      (canon_pc (cHR k hk) (cHR j0 hj0')),
    c1, b1', c2, b2', c3, hfin']
  simp [hw1l, hw1'l, hw2l, hw2'l, hw3l]

theorem plane_ok (ℓ : Nat) (hl : ℓ < 16) (hLK : Nat.beq (lget E3.LK ℓ) 0 = false)
    (hi : lget E3.LI ℓ < 4608) (hiy : lget E3.LY ℓ < 4608)
    (hinv : invEqK 276 9 (mask 9) (Nat.mul 276 9) (HR.E (lget E3.LI ℓ))
      (pinvS 276 9 (mask 9) (HR.E (lget E3.LI ℓ))) = true)
    (hy1 : Nat.beq (HR.E (lget E3.LY ℓ)) (pc (HR.E (lget E3.LI ℓ))
      (pc YP (pinvS 276 9 (mask 9) (HR.E (lget E3.LI ℓ))))) = true)
    (hy2 : Nat.beq (pc (HR.E (lget E3.LY ℓ)) (HR.E (lget E3.LI ℓ)))
      (pc (HR.E (lget E3.LI ℓ)) YP) = true)
    (hy3 : Nat.beq (TPl ℓ (lget E3.LY ℓ)) YP = true) :
    planeBadOK (leafA ℓ) = true := by
  have cH := cHR _ hi
  have cHI : Cn (pinvS 276 9 (mask 9) (HR.E (lget E3.LI ℓ))) := allN_spec kHI ℓ hl
  have hHI := (invEqK_sound hinv).1
  unfold planeBadOK
  dsimp +zetaHave only
  rw [treeTab_leaf ℓ hl, Bool.true_and]
  refine anyLt_of hi ?_
  rw [hList_get _ hi, hHI, y_eq, comp3 cH cY cHI, hIdx_of hiy hy1]
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨decide_eq_true hiy, ?_⟩, ?_⟩, ?_⟩
  · rw [hList_get _ hiy, compA_unpack (cHR _ hiy) cH, compA_unpack cH cY,
      eqA_unpack (canon_pc (cHR _ hiy) cH) (canon_pc cH cY)]
    exact hy2
  · rw [TPl_get ℓ hl _ hiy, eqA_unpack (cTPl ℓ hl _ hiy) cY]
    exact hy3
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    cases hck : commutesA 276 hList[k]! (unpack 276 9 YP)
    · rfl
    · rw [← y_eq] at hck
      rw [Bool.not_true, Bool.false_or, ← y_eq]
      exact chain_ok ℓ hl hLK hi hHI k hk hck

theorem leaf_ok (ℓ : Nat) (hl : ℓ < 16) : leafOK (leafA ℓ) = true := by
  have h := leafH_all ℓ hl
  unfold leafH at h
  simp only [CFSG.KC.Fendel.strictB_eq] at h
  unfold leafOK
  cases hk : Nat.beq (lget E3.LK ℓ) 0
  · rw [hk] at h
    dsimp only at h
    obtain ⟨hi, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hiy, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨_, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hinv, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hy1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hy2, hy3⟩ := (bAnd_iff _ _).1 h
    rw [plane_ok ℓ hl hk (Nat.le_of_ble_eq_true hi) (Nat.le_of_ble_eq_true hiy) hinv hy1 hy2 hy3,
      Bool.or_true]
  · rw [hk] at h
    dsimp only at h
    obtain ⟨hi, h2⟩ := (bAnd_iff _ _).1 h
    rw [psi_ok ℓ hl (Nat.le_of_ble_eq_true hi) h2, Bool.true_or]

theorem l2_pass (k j₂ : Nat) (hk : k < 3) (hj : j₂ < 4608)
    (ht : testK P0 P4 EAP [HR.E (lget E3.R k), HR.E j₂] E3.WS2 = true) :
    E3.P2.contains (4608 * k + j₂) = true := by
  have h := l2_all (4608 * k + j₂) (by omega)
  unfold l2K at h
  rw [CFSG.KC.Fendel.strictB_eq] at h
  have e1 : (4608 * k + j₂) / 4608 = k := by omega
  have e2 : (4608 * k + j₂) % 4608 = j₂ := by omega
  rw [e1, e2] at h
  cases hw : Nat.beq (E3.W2 (4608 * k + j₂)) 1000000
  · rw [hw] at h
    dsimp only at h
    rw [testK_false h] at ht
    exact Bool.noConfusion ht
  · rw [hw] at h
    dsimp only at h
    exact h

theorem l3_pass (t k j₂ j₃ : Nat) (ht8 : t < 8) (hj2 : j₂ < 4608) (hj : j₃ < 4608)
    (hx : lget E3.P2 t = 4608 * k + j₂)
    (ht : testK P0 P4 EAP [HR.E (lget E3.R k), HR.E j₂, HR.E j₃] E3.WS3 = true) :
    E3.P3.contains (4608 * t + j₃) = true := by
  have h := l3_all (4608 * t + j₃) (by omega)
  unfold l3K at h
  rw [CFSG.KC.Fendel.strictB_eq, CFSG.KC.Fendel.strictB_eq] at h
  have e1 : (4608 * t + j₃) / 4608 = t := by omega
  have e2 : (4608 * t + j₃) % 4608 = j₃ := by omega
  have e3 : (4608 * k + j₂) / 4608 = k := by omega
  have e4 : (4608 * k + j₂) % 4608 = j₂ := by omega
  rw [e1, e2, hx, e3, e4] at h
  cases hw : Nat.beq (E3.W3 (4608 * t + j₃)) 1000000
  · rw [hw] at h
    dsimp only at h
    rw [testK_false h] at ht
    exact Bool.noConfusion ht
  · rw [hw] at h
    dsimp only at h
    exact h

theorem l1_spec (j : Nat) (hj : j < 4608) (hb : Nat.beq (E3.TB j) 1 = true) :
    ckF E3.CI E3.MI E3.N j < 3 ∧ ciF E3.CS E3.OFF E3.CI E3.CV E3.MI E3.N j < 4608 ∧
      Nat.beq (pc (HR.E (ciF E3.CS E3.OFF E3.CI E3.CV E3.MI E3.N j)) (HR.E j))
        (pc (HR.E (lget E3.R (ckF E3.CI E3.MI E3.N j)))
          (HR.E (ciF E3.CS E3.OFF E3.CI E3.CV E3.MI E3.N j))) = true := by
  have h := l1_all j hj
  unfold l1K at h
  rw [hb] at h
  obtain ⟨_, h2⟩ := (bAnd_iff _ _).1 h
  rw [CFSG.KC.Fendel.strictB_eq, CFSG.KC.Fendel.strictB_eq] at h2
  obtain ⟨hc', h2⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨hv, heq⟩ := (bAnd_iff _ _).1 h2
  exact ⟨Nat.le_of_ble_eq_true hc', Nat.le_of_ble_eq_true hv, heq⟩

theorem part2 (j : Nat) (hj : j < 4608) :
    (!testsOK #[hList[j]!] wsE1 ||
      (decide ((Array.ofFn (n := 4608) fun j => ckF E3.CI E3.MI E3.N j.val)[j]! < 3) &&
        decide ((Array.ofFn (n := 4608) fun j => ciF E3.CS E3.OFF E3.CI E3.CV E3.MI E3.N j.val)[j]!
          < 4608) &&
        eqA 276 (compA 276
          hList[(Array.ofFn (n := 4608) fun j => ciF E3.CS E3.OFF E3.CI E3.CV E3.MI E3.N j.val)[j]!]!
          hList[j]!)
          (compA 276 hList[E3.R.toArray[(Array.ofFn (n := 4608) fun j =>
              ckF E3.CI E3.MI E3.N j.val)[j]!]!]!
            hList[(Array.ofFn (n := 4608) fun j =>
              ciF E3.CS E3.OFF E3.CI E3.CV E3.MI E3.N j.val)[j]!]!))) = true := by
  cases ht : testsOK #[hList[j]!] wsE1
  · rfl
  · rw [Bool.not_true, Bool.false_or]
    have hb : Nat.beq (E3.TB j) 1 = true := by
      rw [tst_eq j hj, beq_iff_eq] at ht
      rw [ht]
      rfl
    obtain ⟨hc'', hv', heq⟩ := l1_spec j hj hb
    rw [ofFn_get (c := 4608) (fun j => ckF E3.CI E3.MI E3.N j) hj,
      ofFn_get (c := 4608) (fun j => ciF E3.CS E3.OFF E3.CI E3.CV E3.MI E3.N j) hj,
      lget_toArray, hList_get _ hv', hList_get j hj, hList_get _ (R_lt _ hc''),
      compA_unpack (cHR _ hv') (cHR j hj), compA_unpack (cHR _ (R_lt _ hc'')) (cHR _ hv'),
      eqA_unpack (canon_pc (cHR _ hv') (cHR j hj)) (canon_pc (cHR _ (R_lt _ hc'')) (cHR _ hv')),
      heq, decide_eq_true hc'', decide_eq_true hv']
    rfl

theorem part3 (k j₂ j₃ : Nat) (hk : k < 3) (hj₂ : j₂ < 4608) (hj₃ : j₃ < 4608)
    (ht2 : testsOK #[hList[lget E3.R k]!, hList[j₂]!] wsE2 = true)
    (ht3 : testsOK #[hList[lget E3.R k]!, hList[j₂]!, hList[j₃]!] wsE3 = true) :
    leafOK #[hList[lget E3.R k]!, hList[j₂]!, hList[j₃]!] = true := by
  rw [tests2 _ _ (R_lt k hk) hj₂] at ht2
  rw [tests3 _ _ _ (R_lt k hk) hj₂ hj₃] at ht3
  have hx := l2_pass k j₂ hk hj₂ ht2
  obtain ⟨htl, htx⟩ := lget_idxOf hx
  generalize E3.P2.idxOf (4608 * k + j₂) = t at htl htx
  have ht8 : t < 8 := by rw [kIdx.2.2.1] at htl; exact htl
  have hy := l3_pass t k j₂ j₃ ht8 hj₂ hj₃ htx ht3
  obtain ⟨hll, hly⟩ := lget_idxOf hy
  generalize E3.P3.idxOf (4608 * t + j₃) = ℓ at hll hly
  have hl16 : ℓ < 16 := by rw [kIdx.2.2.2.1] at hll; exact hll
  have hI : leafI ℓ = [lget E3.R k, j₂, j₃] := by
    unfold leafI
    have ey1 : (4608 * t + j₃) / 4608 = t := by omega
    have ey2 : (4608 * t + j₃) % 4608 = j₃ := by omega
    have ex1 : (4608 * k + j₂) / 4608 = k := by omega
    have ex2 : (4608 * k + j₂) % 4608 = j₂ := by omega
    rw [hly, ey1, ey2, htx, ex1, ex2]
  have hA : #[hList[lget E3.R k]!, hList[j₂]!, hList[j₃]!] = leafA ℓ := by
    unfold leafA
    rw [leafY_eq _ 0 (by omega), leafY_eq _ 1 (by omega), leafY_eq _ 2 (by omega), hI,
      hList_get _ (R_lt k hk), hList_get _ hj₂, hList_get _ hj₃]
    rfl
  rw [hA]
  exact leaf_ok _ hl16

theorem facts3096 : e3Check = true := by
  unfold e3Check
  dsimp +zetaHave only
  rw [classData_eq]
  have hRl : E3.R.length = 3 := kIdx.2.1
  have hsz : E3.R.toArray.size = 3 := by rw [List.size_toArray, hRl]
  dsimp only
  rw [hsz, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    rw [lget_toArray]
    exact decide_eq_true (R_lt k hk)
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    exact part2
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j₂ hj₂
    rw [lget_toArray]
    cases ht2 : testsOK #[hList[lget E3.R k]!, hList[j₂]!] wsE2
    · rfl
    · rw [Bool.not_true, Bool.false_or, CFSG.Monster.B.Co2.allLt_iff]
      intro j₃ hj₃
      cases ht3 : testsOK #[hList[lget E3.R k]!, hList[j₂]!, hList[j₃]!] wsE3
      · rfl
      · rw [Bool.not_true, Bool.false_or]
        exact part3 k j₂ j₃ hk hj₂ hj₃ ht2 ht3

end CertificateChecks.KernelLC.Co3Id

end
