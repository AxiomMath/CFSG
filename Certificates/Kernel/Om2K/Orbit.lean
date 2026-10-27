module

public import Certificates.Kernel.Om2K.Rel
public import Certificates.Kernel.Om2K.ChecksO
public import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.SetOrb
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab keyF)

noncomputable abbrev V (i : Nat) : Array Nat := codeArr 9 48 (Orb.C i)

theorem orbOKc_all : ∀ c < 63, orbOKc c = true := by
  intro c hc
  interval_cases c
  exacts [orbOKc0, orbOKc1, orbOKc2, orbOKc3, orbOKc4, orbOKc5, orbOKc6, orbOKc7, orbOKc8,
    orbOKc9, orbOKc10, orbOKc11, orbOKc12, orbOKc13, orbOKc14, orbOKc15, orbOKc16, orbOKc17,
    orbOKc18, orbOKc19, orbOKc20, orbOKc21, orbOKc22, orbOKc23, orbOKc24, orbOKc25, orbOKc26,
    orbOKc27, orbOKc28, orbOKc29, orbOKc30, orbOKc31, orbOKc32, orbOKc33, orbOKc34, orbOKc35,
    orbOKc36, orbOKc37, orbOKc38, orbOKc39, orbOKc40, orbOKc41, orbOKc42, orbOKc43, orbOKc44,
    orbOKc45, orbOKc46, orbOKc47, orbOKc48, orbOKc49, orbOKc50, orbOKc51, orbOKc52, orbOKc53,
    orbOKc54, orbOKc55, orbOKc56, orbOKc57, orbOKc58, orbOKc59, orbOKc60, orbOKc61, orbOKc62]

theorem orb_facts {i : Nat} (hi : i < 6300) :
    codeOK 480 9 48 (Orb.C i) (Orb.M i) = true ∧
      closK 9 48 8 6300 L.G Orb.C Orb.M (fun j => j) Orb.E i = true ∧
      treeK 9 48 8 L.G Orb.C Orb.M (fun j => j) Orb.D i = true := by
  have h := allN_spec (orbOKc_all (i / 100) (by omega)) (i % 100) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 100 (i / 100)) (i % 100) = i := Nat.div_add_mod i 100
  rw [e] at h
  unfold orbOK at h
  obtain ⟨h1, h2⟩ := band h
  exact ⟨h1, band h2⟩

theorem code_ok {i : Nat} (hi : i < 6300) : codeOK 480 9 48 (Orb.C i) (Orb.M i) = true :=
  (orb_facts hi).1

theorem inj_of_ok {P : Nat} (h : okK P = true) :
    ∀ a < 480, ∀ b < 480, pg 9 (mask 9) P a = pg 9 (mask 9) P b → a = b := by
  have h2 := (invEqK_sound (okK_iff h).2.1).2
  unfold isInvA at h2
  rw [allLt_true] at h2
  intro a ha b hb e
  have ea := h2 a ha
  have eb := h2 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at ea eb
  rw [CFSG.KC.SetOrb.unpack_get ha] at ea
  rw [CFSG.KC.SetOrb.unpack_get hb] at eb
  rw [← ea.2, ← eb.2, e]

theorem act_eq {P i j : Nat} (hP : okK P = true) (hi : i < 6300) (hj : j < 6300)
    (h : imgK 9 48 P (Orb.C i) = Orb.M j) : actFY (unpack 480 9 P) (V i) = V j :=
  act_code (inj_of_ok hP) (code_ok hi) (code_ok hj) h

theorem validFY_codeArr {w len C M : Nat} (h : codeOK 480 w len C M = true) :
    validFY (codeArr w len C) = true := by
  obtain ⟨c1, c2, -⟩ := codeOK_facts h
  have hs : (codeArr w len C).size = len := codeArr_size _ _ _
  unfold validFY
  rw [Bool.and_eq_true, Array.all_eq_true, List.all_eq_true]
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have ht' : t < len := hs ▸ ht
    rw [← getElem!_pos _ t ht, codeArr_get ht']
    exact decide_eq_true (c1 t ht')
  · rw [List.mem_range, hs] at ht
    rw [codeArr_get (by omega), codeArr_get (by omega)]
    exact decide_eq_true (c2 t (by omega))

theorem valid_V {i : Nat} (hi : i < 6300) : validFY (V i) = true := validFY_codeArr (code_ok hi)

theorem key_V (i : Nat) : keyF (V i) = keyK 240 9 48 (Orb.C i) := foldl_code 240 9 _ 48

theorem key_inj {a b : Nat} (ha : a < 6300) (hb : b < 6300) (h : keyF (V a) = keyF (V b)) : a = b := by
  rw [key_V, key_V] at h
  exact distinctK_inj kDist a ha b hb h

theorem cert_of {gs : Array (Array Nat)} {ng N fuel : Nat} {G X Y E D : Nat → Nat}
    {root : Array Nat}
    (hgs : ∀ k < ng, gs[k]! = unpack 480 9 (G k)) (hok : ∀ k < ng, okK (G k) = true)
    (hX : ∀ i < N, X i < 6300) (hcl : ∀ i < N, closK 9 48 ng N G Orb.C Orb.M X E i = true)
    (htr : ∀ i < N, treeK 9 48 ng G Orb.C Orb.M X D i = true) (hinv : ∀ i < N, Y (X i) = i)
    (h0 : 0 < N) (hroot : V (X 0) = root) (hf : N ≤ fuel) :
    arrCertOK (fun k F => actFY gs[k]! F) ng validFY keyF root
        (arrBfs (fun k F => actFY gs[k]! F) ng keyF root fuel) = true ∧
      (∀ x, x ∈ (arrBfs (fun k F => actFY gs[k]! F) ng keyF root fuel).pts ↔
        ∃ i < N, V (X i) = x) ∧
      (arrBfs (fun k F => actFY gs[k]! F) ng keyF root fuel).pts.size = N := by
  refine orbit_of_pinned (V := fun i => V (X i)) (par := fun i => D i % 65536)
    (lab := fun i => D i / 65536) h0 hroot ?_ ?_ (fun i hi => valid_V (hX i hi)) ?_ ?_ hf
  · intro i hi k hk
    obtain ⟨j, hj, e⟩ := closK_spec (hcl i hi) k hk
    refine ⟨j, hj, ?_⟩
    rw [hgs k hk]
    exact act_eq (hok k hk) (hX i hi) (hX j hj) e
  · intro i hi hpos
    obtain ⟨hp, hl, e⟩ := treeK_spec (htr i hi) hpos
    refine ⟨hp, hl, ?_⟩
    rw [hgs _ hl]
    exact (act_eq (hok _ hl) (hX _ (by omega)) (hX i hi) e).symm
  · intro a ha b hb e
    rw [key_inj (hX a ha) (hX b hb) e]
  · intro a ha b hb e
    have e2 := key_inj (hX a ha) (hX b hb) (by rw [e])
    rw [← hinv a ha, ← hinv b hb, e2]

theorem genY_size : (genY (reflTab ())).size = 8 := by simp [genY]

theorem genY_L {k : Nat} (hk : k < 8) : (genY (reflTab ()))[k]! = unpack 480 9 (L.G k) := by
  rw [genY_get hk, Nat.eq_of_beq_eq_true (allN_spec kGY k hk)]

theorem F0_eq : fCodeY (wY LY wT0) = V 0 := by
  unfold fCodeY
  rw [t0_eq, cA_eq (by norm_num)]
  exact filter_code (code_ok (by norm_num)) (Nat.eq_of_beq_eq_true kF0)

theorem main_cert :
    arrCertOK (fun k F => actFY (genY (reflTab ()))[k]! F) 8 validFY keyF (V 0)
        (arrBfs (fun k F => actFY (genY (reflTab ()))[k]! F) 8 keyF (V 0) 6301) = true ∧
      (∀ x, x ∈ (arrBfs (fun k F => actFY (genY (reflTab ()))[k]! F) 8 keyF (V 0) 6301).pts ↔
        ∃ i < 6300, V i = x) ∧
      (arrBfs (fun k F => actFY (genY (reflTab ()))[k]! F) 8 keyF (V 0) 6301).pts.size = 6300 :=
  cert_of (X := fun j => j) (Y := fun j => j) (E := Orb.E) (D := Orb.D) (G := L.G)
    (fun k hk => genY_L hk) (fun k hk => L_ok (by omega)) (fun i hi => hi)
    (fun i hi => (orb_facts hi).2.1) (fun i hi => (orb_facts hi).2.2) (fun i _ => rfl)
    (by norm_num) rfl (by norm_num)

theorem orbit_k : orbitCheckY (reflTab ()) = true := by
  unfold orbitCheckY orbSizeY orbFY
  simp only [Bool.and_eq_true]
  rw [F0_eq, genY_size]
  obtain ⟨h1, -, h3⟩ := main_cert
  refine ⟨valid_V (by norm_num), h1, ?_⟩
  rw [h3]
  rfl

end CertificateChecks.KernelOm2

end
