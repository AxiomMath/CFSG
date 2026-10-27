module

public import Certificates.Kernel.Om2K.Rel
public import Certificates.Kernel.Om2K.ChecksE
public import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab)

theorem keyPtsY_lt : ∀ p ∈ keyPtsYA.toList, p < 480 := by decide

theorem enum_of {ws : List (List Nat)} {ng N sz : Nat} {G T E S : Nat → Nat} {SK : List Nat}
    (hlt : ∀ w ∈ ws, ∀ l ∈ w, l < 16) (hlen : ws.length = ng)
    (hG : allN ng (genOK ws G) = true) (hk : bfsK 480 9 ng G N T E S = true)
    (hK : keysSK 480 9 keyPtsYA.toList N T SK = true) (hN : N = sz) :
    enumOK 480 (ws.map (wY LY)).toArray keyPtsY (enumOfY LY ws (sz + 1)) = true ∧
      (enumOfY LY ws (sz + 1)).pts = Array.ofFn (n := N) fun i => unpack 480 9 (T i.val) := by
  have hg1 : ∀ k < ng, Nat.beq (G k) (wYK (ws.getD k [])) = true ∧ okK (G k) = true :=
    fun k hk => band (allN_spec hG k hk)
  have hs : (ws.map (wY LY)).toArray.size = ng := by simp [hlen]
  have hgs : ∀ k < ng, (ws.map (wY LY)).toArray[k]! = unpack 480 9 (G k) := by
    intro k hk
    rw [getElem!_pos _ k (by rw [hs]; exact hk)]
    simp only [List.getElem_toArray, List.getElem_map]
    rw [← List.getD_eq_getElem _ [] (by omega)]
    exact tab_eq hlt (fun j hj => (hg1 j (by omega)).1) (by omega)
  have hp : ∀ k < ng, permOK 480 9 (mask 9) (480 * 9) (G k) (pinvS 480 9 (mask 9) (G k)) = true :=
    fun k hk => (okK_iff (hg1 k hk).2).2.1
  exact ⟨enumOK_of_bfsK_base hs hgs hp hk keyPtsY_lt hK (by omega),
    enumBfs_pts_base hs hgs hk keyPtsY_lt hK (by omega)⟩

theorem enumSize_of {ws : List (List Nat)} {ng N sz : Nat} {G T E S : Nat → Nat} {SK : List Nat}
    (hlt : ∀ w ∈ ws, ∀ l ∈ w, l < 16) (hlen : ws.length = ng)
    (hG : allN ng (genOK ws G) = true) (hk : bfsK 480 9 ng G N T E S = true)
    (hK : keysSK 480 9 keyPtsYA.toList N T SK = true) (hN : N = sz) : enumSizeY LY ws sz = true := by
  obtain ⟨h1, h2⟩ := enum_of hlt hlen hG hk hK hN
  unfold enumSizeY
  simp only [Bool.and_eq_true]
  refine ⟨h1, ?_⟩
  rw [h2, Array.size_ofFn, hN]
  exact beq_self_eq_true _

theorem okE0 : bfsK 480 9 E0.ng E0.G E0.N E0.T E0.E E0.S = true :=
  bfsK_of_slices (L := 64) (K := 64) (C := E0.C) (by decide) (by norm_num) kSz E0.g E0.csAll E0.t0
    E0.dist (Nat.eq_of_beq_eq_true E0.c0) (Nat.eq_of_beq_eq_true E0.cK) E0.rsAll

theorem okE1 : bfsK 480 9 E1.ng E1.G E1.N E1.T E1.E E1.S = true :=
  bfsK_of_slices (L := 27) (K := 1) (C := E1.C) (by decide) (by norm_num) kSz E1.g E1.csAll E1.t0
    E1.dist (Nat.eq_of_beq_eq_true E1.c0) (Nat.eq_of_beq_eq_true E1.cK) E1.rsAll

theorem okE2 : bfsK 480 9 E2.ng E2.G E2.N E2.T E2.E E2.S = true :=
  bfsK_of_slices (L := 64) (K := 16) (C := E2.C) (by decide) (by norm_num) kSz E2.g E2.csAll E2.t0
    E2.dist (Nat.eq_of_beq_eq_true E2.c0) (Nat.eq_of_beq_eq_true E2.cK) E2.rsAll

theorem okE3 : bfsK 480 9 E3.ng E3.G E3.N E3.T E3.E E3.S = true :=
  bfsK_of_slices (L := 3) (K := 1) (C := E3.C) (by decide) (by norm_num) kSz E3.g E3.csAll E3.t0
    E3.dist (Nat.eq_of_beq_eq_true E3.c0) (Nat.eq_of_beq_eq_true E3.cK) E3.rsAll

theorem okE4 : bfsK 480 9 E4.ng E4.G E4.N E4.T E4.E E4.S = true :=
  bfsK_of_slices (L := 64) (K := 72) (C := E4.C) (by decide) (by norm_num) kSz E4.g E4.csAll E4.t0
    E4.dist (Nat.eq_of_beq_eq_true E4.c0) (Nat.eq_of_beq_eq_true E4.cK) E4.rsAll

theorem wS0_lt : ∀ w ∈ wS0, ∀ l ∈ w, l < 16 := by decide
theorem wP3_lt : ∀ w ∈ wP3, ∀ l ∈ w, l < 16 := by decide
theorem wSc_lt : ∀ w ∈ wSc, ∀ l ∈ w, l < 16 := by decide
theorem wPc_lt : ∀ w ∈ wPc, ∀ l ∈ w, l < 16 := by decide

theorem enum_k : enumCheckY (reflTab ()) = true := by
  unfold enumCheckY
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨enumSize_of wS0_lt (by decide) kEG0 okE0 E0.keys rfl,
    enumSize_of wP3_lt (by decide) kEG1 okE1 E1.keys rfl⟩,
    enumSize_of wSc_lt (by decide) kEG2 okE2 E2.keys rfl⟩,
    enumSize_of wPc_lt (by decide) kEG3 okE3 E3.keys rfl⟩,
    enumSize_of wCR_lt (by decide) kEG4 okE4 E4.keys rfl⟩

end CertificateChecks.KernelOm2

end
