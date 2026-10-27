module

public import CFSG.Certificates.Kernel.W4C2Sound
public import Certificates.Kernel.W4C2.Inj
public import Certificates.Kernel.W4C2.Val
public import Certificates.Kernel.W4C2.Stab
public import Certificates.Kernel.W4C2.Local
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.KernelW4C2

open CFSG.GF2Type.Smith1979.W4C2 LocalTest CFSG.KC.W4C2K

theorem all16 {f : Nat → Bool} (h0 : f 0 = true) (h1 : f 1 = true) (h2 : f 2 = true)
    (h3 : f 3 = true) (h4 : f 4 = true) (h5 : f 5 = true) (h6 : f 6 = true) (h7 : f 7 = true)
    (h8 : f 8 = true) (h9 : f 9 = true) (h10 : f 10 = true) (h11 : f 11 = true)
    (h12 : f 12 = true) (h13 : f 13 = true) (h14 : f 14 = true) (h15 : f 15 = true) :
    ∀ i < 16, f i = true
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3 | 4, _ => h4 | 5, _ => h5 | 6, _ => h6
  | 7, _ => h7 | 8, _ => h8 | 9, _ => h9 | 10, _ => h10 | 11, _ => h11 | 12, _ => h12
  | 13, _ => h13 | 14, _ => h14 | 15, _ => h15 | _ + 16, h => absurd h (by omega)

theorem inj_all : ∀ i < 16, (List.range' (4096 * i) 4096).filter injK = GL.getD i [] := by
  intro i hi
  have h := all16 ch330390inj0 ch330390inj1 ch330390inj2 ch330390inj3 ch330390inj4
    ch330390inj5 ch330390inj6 ch330390inj7 ch330390inj8 ch330390inj9 ch330390inj10
    ch330390inj11 ch330390inj12 ch330390inj13 ch330390inj14 ch330390inj15 i hi
  unfold ch330390inj at h
  exact eq_of_beq h

theorem val_all : ∀ i < 16, ∀ n ∈ GL.getD i [], validK (mk n (dualK n) false) = true := by
  intro i hi
  have h := all16 ch330390val0 ch330390val1 ch330390val2 ch330390val3 ch330390val4
    ch330390val5 ch330390val6 ch330390val7 ch330390val8 ch330390val9 ch330390val10
    ch330390val11 ch330390val12 ch330390val13 ch330390val14 ch330390val15 i hi
  unfold ch330390val at h
  exact List.all_eq_true.mp h

theorem pn_all : ∀ i < 16, (GL.getD i []).flatMap (stabPK bNK) = PNs.getD i [] := by
  intro i hi
  have h := all16 ch330390pn0 ch330390pn1 ch330390pn2 ch330390pn3 ch330390pn4
    ch330390pn5 ch330390pn6 ch330390pn7 ch330390pn8 ch330390pn9 ch330390pn10
    ch330390pn11 ch330390pn12 ch330390pn13 ch330390pn14 ch330390pn15 i hi
  unfold ch330390pn at h
  exact eq_of_beq h

theorem pm_all : ∀ i < 16, (GL.getD i []).flatMap (stabPK bMK) = PMs.getD i [] := by
  intro i hi
  have h := all16 ch330390pm0 ch330390pm1 ch330390pm2 ch330390pm3 ch330390pm4
    ch330390pm5 ch330390pm6 ch330390pm7 ch330390pm8 ch330390pm9 ch330390pm10
    ch330390pm11 ch330390pm12 ch330390pm13 ch330390pm14 ch330390pm15 i hi
  unfold ch330390pm at h
  exact eq_of_beq h

theorem hGL : (List.range 65536).filter injK = (List.range 16).flatMap fun i => GL.getD i [] :=
  filter_chunks inj_all

theorem stab_eq (b : Nat × Nat) (Q : List (List Nat))
    (hQ : ∀ i < 16, (GL.getD i []).flatMap (stabPK b) = Q.getD i []) :
    (stabL (Hlist ()) b).map cd = (List.range 16).flatMap fun i => Q.getD i [] := by
  rw [stab_map, Hlist_map, List.filter_flatMap]
  rw [flatMap_congr' (g := stabPK b) (fun n hn => by
    rw [List.mem_filter, List.mem_range] at hn
    exact hpair_filter hn.1 b)]
  rw [hGL, List.flatMap_assoc]
  exact flatMap_congr' fun i hi => hQ i (List.mem_range.mp hi)

theorem hPN : (stabL (Hlist ()) bN).map cd = PN :=
  (stab_eq bNK PNs pn_all).trans (eq_of_beq ch330390pnJoin)

theorem hPM : (stabL (Hlist ()) bM).map cd = PM :=
  (stab_eq bMK PMs pm_all).trans (eq_of_beq ch330390pmJoin)

theorem valid_all : (Hlist ()).all validE = true := by
  rw [List.all_eq_true]
  intro E hE
  obtain ⟨n, hn, hi, s, rfl⟩ := mem_Hlist hE
  rw [validE_eq, cd_rowsOf hn]
  have hd : dualK n < 65536 := tr_lt _
  have hv : validK (mk n (dualK n) s) = validK (mk n (dualK n) false) := by
    unfold validK
    rw [gK_mk s hn hd, hK_mk s hn hd, gK_mk false hn hd, hK_mk false hn hd]
  rw [hv]
  have hmem : n ∈ GL.getD (n / 4096) [] := by
    rw [← inj_all (n / 4096) (by omega), List.mem_filter, List.mem_range'_1]
    exact ⟨by omega, hi⟩
  exact val_all (n / 4096) (by omega) n hmem

theorem orb_all : orbOK (Hlist ()) = true := by
  unfold orbOK
  rw [List.all_eq_true]
  intro n hn
  rw [List.mem_range] at hn
  have h := ch330390orb
  unfold orbWK at h
  have h1 := List.all_eq_true.mp h n (List.mem_range.mpr hn)
  unfold orbWK.orb1K at h1
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at h1 ⊢
  rcases h1 with (h1 | h1) | ⟨⟨hlt, hinj⟩, heq⟩
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr (by rw [dot4_eq]; exact h1))
  · refine Or.inr (List.any_eq_true.mpr ⟨_, mem_Hlist_of hlt hinj (WIT.getD n 0 % 2 == 1), ?_⟩)
    rw [eqV_appE, cd_rowsOf hlt]
    by_cases hc : (n % 16 == 0) = true ∨ (n / 16 == 0) = true
    · have hc' : (n % 16 == 0 || n / 16 == 0) = true := by simpa [Bool.or_eq_true] using hc
      rw [if_pos hc]
      rw [hc'] at heq
      exact heq
    · have hc' : (n % 16 == 0 || n / 16 == 0) = false := by simpa [Bool.or_eq_true] using hc
      rw [if_neg hc]
      rw [hc'] at heq
      exact heq

theorem chk_true : chk = true := by
  unfold chk
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨valid_all, orb_all⟩, ?_⟩, ?_⟩
  · rw [chkN_eq, hPN, eq_of_beq ch330390un]; exact ch330390chkN
  · rw [chkM_eq, hPM, eq_of_beq ch330390cl]; exact ch330390chkM

end CertificateChecks.KernelW4C2
