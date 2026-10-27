module

public import Certificates.Kernel.SporSch.Co2M.EnumP0
public import CFSG.Certificates.Kernel.SporSch.Co2LESound
public import CFSG.Sporadic.Co2Schreier.ThreeCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ThreeCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.Co2LE CFSG.Sporadic.Co2Schreier
open CFSG.KS.MatRep CFSG.KS.MatInj CFSG.RankThree.Native.F2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Co2Cert

theorem p0_words_ok : wordsOK cT.length p0Words = true := by
  rw [c_len]
  decide +kernel

theorem p0Rep : RepT 22 co2PackedVecs p0Arrs p0T :=
  repT_words good V_size mmK_eq I22_eq cRep p0_words_ok

theorem p0_len : p0T.length = 2 := by
  have h : p0Words.length = 2 := by decide
  rw [p0T, List.length_map, h]

theorem p0gens : GensRep co2PackedVecs p0Arrs P0G 2 := by
  refine ⟨by rw [p0Rep.1, p0_len], fun j hj => ⟨(p0T.getD j (0, 0)).2, ?_⟩⟩
  rw [Nat.eq_of_beq_eq_true (allN_spec p0g_ok j hj)]
  exact repT_get p0Rep (by rw [p0_len]; exact hj)

theorem p0recs : Recs P0R P0G (PV 0) 2 81 := by
  obtain ⟨h1, h2⟩ := (bAnd_iff (Nat.beq (eM P0R 0) I22) (Nat.beq (mR P0R 2 0) 1)).1 p0head_ok
  exact ⟨allN_spec p0recs_ok, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, by norm_num⟩

theorem p0f : (leftEnum p0Arrs 81).elems = LL co2PackedVecs P0R 81 ∧
    enumOK p0Arrs 81 (leftEnum p0Arrs 81) = true ∧
    ∀ k < 81, ∃ M', Rep 22 co2PackedVecs (LL co2PackedVecs P0R 81)[k]! (eM P0R k) M' :=
  leftEnum_facts vok p0recs p0gens (le_refl 81)

theorem qf : (leftEnum qArrs 512).elems = LL co2PackedVecs QR 512 ∧
    enumOK qArrs 512 (leftEnum qArrs 512) = true ∧
    ∀ k < 512, ∃ M', Rep 22 co2PackedVecs (LL co2PackedVecs QR 512)[k]! (eM QR k) M' :=
  leftEnum_facts vok qrecs qgens (le_refl 512)

theorem commA_mat {a b : Array ℕ} {A A' B B' : ℕ} (ha : Rep 22 co2PackedVecs a A A')
    (hb : Rep 22 co2PackedVecs b B B') : commA a b = Nat.beq (mmK B A) (mmK A B) := by
  have r1 := rep_compA good ha hb
  have r2 := rep_compA good hb ha
  unfold commA
  rw [← V_size, r1.1, r2.1, eqA_permOfMat spans r1.2.1 r2.2.1 (mmul_lt _ _) (mmul_lt _ _),
    mmK_eq, mmK_eq]

theorem p0_elems : enumP0.elems = LL co2PackedVecs P0R 81 := p0f.1

theorem q_elems : enumQ.elems = LL co2PackedVecs QR 512 := qf.1

theorem p0_rep {k : ℕ} (hk : k < 81) :
    ∃ M', Rep 22 co2PackedVecs (LL co2PackedVecs P0R 81)[k]! (eM P0R k) M' := p0f.2.2 k hk

theorem q_rep {k : ℕ} (hk : k < 512) :
    ∃ M', Rep 22 co2PackedVecs (LL co2PackedVecs QR 512)[k]! (eM QR k) M' := qf.2.2 k hk

theorem cent_eq (k : ℕ) (hk : k < 81) : p0CentIdx k = centM k := by
  unfold p0CentIdx centM
  refine List.filter_congr fun j hj => ?_
  obtain ⟨Mk, hMk⟩ := p0_rep hk
  obtain ⟨Mj, hMj⟩ := p0_rep (List.mem_range.1 hj)
  rw [p0_elems, commA_mat hMj hMk]

theorem marked : p0MarkedIdx = [0, 1, 3, 20, 22, 28, 30, 32, 34, 35, 39, 41, 43, 45, 46, 49, 50,
    54, 56, 57, 60, 61, 64, 68, 69, 72, 76] := by
  have h : p0MarkedIdx = (List.range 81).filter (fun k => decide (27 ≤ (centM k).length)) := by
    unfold p0MarkedIdx
    refine List.filter_congr fun k hk => ?_
    rw [cent_eq k (List.mem_range.1 hk)]
  rw [h]
  exact beq_iff_eq.1 marked_ok

theorem entry0 : (LL co2PackedVecs P0R 81)[0]! = idA 2300 := by
  rw [LL_get P0R p0recs.pos, p0recs.zero, I22_eq,
    permOfMat_idM good.hd good.nodup good.lt, V_size]

theorem cube : eqA 2300 (compA 2300 enumP0.elems[4]! (compA 2300 enumP0.elems[4]!
    enumP0.elems[4]!)) (idA 2300) = false := by
  rw [p0_elems, ← entry0]
  obtain ⟨M4, h4⟩ := p0_rep (by norm_num : 4 < 81)
  obtain ⟨M0, h0⟩ := p0_rep (by norm_num : 0 < 81)
  have r1 := rep_compA good h4 h4
  rw [V_size] at r1
  have r2 := rep_compA good h4 r1
  rw [V_size] at r2
  rw [r2.1, h0.1]
  rw [← V_size, eqA_permOfMat spans r2.2.1 h0.2.1 (mmul_lt _ _) (eM_lt _ _), p0recs.zero,
    ← mmK_eq, ← mmK_eq]
  exact cube_ok

theorem six_entry {k : ℕ} (hk : k < 81) (rows : List ℕ) : p0SixOK k rows = sixM k rows := by
  unfold p0SixOK sixM
  obtain ⟨Mk, hMk⟩ := p0_rep hk
  refine allLt_congr fun j _ => ?_
  rw [p0_elems, sixImage_rep hMk]

theorem six : p0SixOK 56 [1, 55, 49, 61, 63, 32] = true ∧ p0SixOK 1 [43, 34, 5, 14, 54, 45] = true ∧
    p0SixOK 20 [1, 57, 30, 20, 2, 7] = true := by
  rw [six_entry (by norm_num), six_entry (by norm_num), six_entry (by norm_num)]
  have h := six_ok
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem qcent : qCentIdx56 = [0, 23] := by
  have h : qCentIdx56 = (List.range 512).filter (fun k =>
      Nat.beq (mmK (eM P0R 56) (eM QR k)) (mmK (eM QR k) (eM P0R 56))) := by
    unfold qCentIdx56
    refine List.filter_congr fun k hk => ?_
    obtain ⟨Mk, hMk⟩ := q_rep (List.mem_range.1 hk)
    obtain ⟨M56, h56⟩ := p0_rep (by norm_num : 56 < 81)
    rw [q_elems, p0_elems, commA_mat hMk h56]
  rw [h]
  exact beq_iff_eq.1 p0qcent_ok

open Certificates in
open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Monster.B.Mathieu in
theorem facts719101 : enumOK p0Arrs 81 enumP0 = true
    ∧ p0MarkedIdx = [0, 1, 3, 20, 22, 28, 30, 32, 34, 35, 39, 41, 43, 45, 46, 49, 50, 54, 56, 57,
        60, 61, 64, 68, 69, 72, 76]
    ∧ eqA 2300 (compA 2300 enumP0.elems[4]! (compA 2300 enumP0.elems[4]! enumP0.elems[4]!))
        (idA 2300) = false
    ∧ (p0SixOK 56 [1, 55, 49, 61, 63, 32] = true ∧ p0SixOK 1 [43, 34, 5, 14, 54, 45] = true ∧
        p0SixOK 20 [1, 57, 30, 20, 2, 7] = true)
    ∧ qCentIdx56 = [0, 23] :=
  ⟨p0f.2.1, marked, cube, six, qcent⟩

end CertificateChecks.KernelSporSch.Co2M

end
