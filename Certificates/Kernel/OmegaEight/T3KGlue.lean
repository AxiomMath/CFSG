module

public import Certificates.Kernel.OmegaEight.T3KChecks
public import Certificates.Kernel.OmegaEight.E9KGlue
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.BfsPinSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.T3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.PGrp
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.HardMathSupport.Curtis.Coordinator
open CFSG.EvenSmallLie.OmegaEight (genArrs)
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord getElem!_map')
open CertificateChecks.KernelO8 CertificateChecks.KernelO8.E9K

theorem nums' : T3R.ng = 4 ∧ T3R.N = 729 ∧ ∀ k < 3, T3R.G k = E9Q.G k := by
  have h := nums
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2,
    fun k hk => Nat.eq_of_beq_eq_true (allN_spec h.2 k hk)⟩

theorem psRLt : ∀ p ∈ psR, p < 360 := by decide

theorem permA : ∀ j < 10, permB 360 9 (AP.S j) = true := allN_spec perm

theorem genA : ∀ j < 10, genArrs[j]! = unpack 360 9 (AP.S j) := genAP.2

theorem qgen {k : ℕ} (hk : k < 3) :
    (triQGens triData)[k]! = unpack 360 9 (E9Q.G k) ∧ permB 360 9 (E9Q.G k) = true := by
  have hk' : k < triData.qW.size := by rw [sizes.1]; exact hk
  obtain ⟨e, p⟩ := posWord_unpack hw9 genA permA
    (fun l hl => (letters_of_toList lettersQ k hk' l hl).trans (by norm_num))
  rw [(map_get wordsQ).2 k hk] at e p
  refine ⟨?_, p⟩
  rw [triQGens, getElem!_map' _ _ hk']
  exact e

theorem qsize : (triQGens triData).size = 3 := by rw [triQGens, Array.size_map, sizes.1]

theorem xgen : posWord 360 genArrs triData.xW = unpack 360 9 (T3R.G 3) ∧
    permB 360 9 (T3R.G 3) = true := by
  have hl : ∀ l ∈ triData.xW, l < 10 := fun l hl => by
    simpa using List.all_eq_true.1 lettersX l hl
  obtain ⟨e, p⟩ := posWord_unpack hw9 genA permA hl
  rw [wordX] at e p
  exact ⟨e, p⟩

theorem rsize : (triRGens triData).size = 4 := by rw [triRGens, Array.size_push, qsize]

theorem rgen {k : ℕ} (hk : k < 4) :
    (triRGens triData)[k]! = unpack 360 9 (T3R.G k) ∧ permB 360 9 (T3R.G k) = true := by
  by_cases h3 : k < 3
  · have e : (triRGens triData)[k]! = (triQGens triData)[k]! := by
      rw [getElem!_pos _ k (by rw [rsize]; exact hk), getElem!_pos _ k (by rw [qsize]; exact h3)]
      simp [triRGens, Array.getElem_push_lt (by rw [qsize]; exact h3)]
    rw [e, nums'.2.2 k h3]
    exact qgen h3
  · have hk3 : k = 3 := by omega
    subst hk3
    have e : (triRGens triData)[3]! = posWord 360 genArrs triData.xW := by
      rw [getElem!_pos _ 3 (by rw [rsize]; norm_num)]
      have h := qsize
      simp only [triRGens] at h ⊢
      simp [Array.getElem_push, h]
    rw [e]
    exact xgen

theorem hgen {k : ℕ} (hk : k < 32) :
    (triHArrs triData)[k]! = unpack 360 9 (T3H k) ∧ permB 360 9 (T3H k) = true := by
  have hk' : k < triData.hW.size := by rw [sizes.2.1]; exact hk
  obtain ⟨e, p⟩ := posWord_unpack hw9 genA permA (letters_of_toList lettersH k hk')
  rw [(map_get wordsH).2 k hk] at e p
  refine ⟨?_, p⟩
  rw [triHArrs, getElem!_map' _ _ hk']
  exact e

theorem hsize : (triHArrs triData).size = 32 := by rw [triHArrs, Array.size_map, sizes.2.1]

theorem ygen {k : ℕ} (hk : k < 32) :
    (triYArrs triData)[k]! = unpack 360 9 (T3Y k) ∧ permB 360 9 (T3Y k) = true := by
  have hk' : k < triData.yW.size := by rw [sizes.2.2.1]; exact hk
  obtain ⟨e, p⟩ := posWord_unpack hw9 (fun l hl => (qgen hl).1) (fun l hl => (qgen hl).2)
    (letters_of_toList lettersY k hk')
  rw [(map_get wordsY).2 k hk] at e p
  refine ⟨?_, p⟩
  rw [triYArrs, getElem!_map' _ _ hk']
  exact e

theorem zgen {k : ℕ} (hk : k < 32) :
    (triZArrs triData)[k]! = unpack 360 9 (T3Z k) ∧ permB 360 9 (T3Z k) = true := by
  have hk' : k < triData.zW.size := by rw [sizes.2.2.2]; exact hk
  obtain ⟨e, p⟩ := posWord_unpack hw9 (fun l hl => (qgen hl).1) (fun l hl => (qgen hl).2)
    (letters_of_toList lettersZ k hk')
  rw [(map_get wordsZ).2 k hk] at e p
  refine ⟨?_, p⟩
  rw [triZArrs, getElem!_map' _ _ hk']
  exact e

theorem q_gens : (triQGens triData).size = E9Q.ng ∧
    ∀ k < E9Q.ng, (triQGens triData)[k]! = unpack 360 9 (E9Q.G k) := by
  rw [E9K.nums'.1]
  exact ⟨qsize, fun k hk => (qgen hk).1⟩

theorem r_gens : (triRGens triData).size = T3R.ng ∧
    ∀ k < T3R.ng, (triRGens triData)[k]! = unpack 360 9 (T3R.G k) := by
  rw [nums'.1]
  exact ⟨rsize, fun k hk => (rgen hk).1⟩

theorem r_perm : ∀ k < T3R.ng,
    permOK 360 9 (mask 9) (360 * 9) (T3R.G k) (pinvS 360 9 (mask 9) (T3R.G k)) = true := by
  rw [nums'.1]
  exact fun k hk => (rgen hk).2

theorem qKeys_eq : triData.qKeys = ps := rfl

theorem rKeys_eq : triData.rKeys = psR := rfl

theorem q_pts : (triQCert triData).pts =
    Array.ofFn (n := E9Q.N) fun i => unpack 360 9 (E9Q.T i.val) := by
  unfold triQCert
  rw [qKeys_eq]
  exact enumBfs_pts_base q_gens.1 q_gens.2 E9Q.ok psLt keysQ (by rw [E9K.nums'.2.1]; decide)

theorem q_enum : enumOK 360 (triQGens triData) ps (triQCert triData) = true := by
  unfold triQCert
  rw [qKeys_eq]
  exact enumOK_of_bfsK_base q_gens.1 q_gens.2 E9K.q_perm E9Q.ok psLt keysQ
    (by rw [E9K.nums'.2.1]; decide)

theorem r_pts : (triRCert triData).pts =
    Array.ofFn (n := T3R.N) fun i => unpack 360 9 (T3R.T i.val) := by
  unfold triRCert
  rw [rKeys_eq]
  exact enumBfs_pts_base r_gens.1 r_gens.2 T3R.ok psRLt keysR (by rw [nums'.2.1]; decide)

theorem r_enum : enumOK 360 (triRGens triData) psR (triRCert triData) = true := by
  unfold triRCert
  rw [rKeys_eq]
  exact enumOK_of_bfsK_base r_gens.1 r_gens.2 r_perm T3R.ok psRLt keysR
    (by rw [nums'.2.1]; decide)

theorem q_size : (triQCert triData).pts.size = 243 := by
  rw [q_pts, Array.size_ofFn, E9K.nums'.2.1]

theorem r_size : (triRCert triData).pts.size = 729 := by rw [r_pts, Array.size_ofFn, nums'.2.1]

theorem q_get : ∀ i < 243, (triQCert triData).pts[i]! = unpack 360 9 (E9Q.T i) := fun i hi => by
  rw [q_pts, getElem!_pos _ i (by rw [Array.size_ofFn, E9K.nums'.2.1]; exact hi),
    Array.getElem_ofFn]

theorem r_get : ∀ i < 729, (triRCert triData).pts[i]! = unpack 360 9 (T3R.T i) := fun i hi => by
  rw [r_pts, getElem!_pos _ i (by rw [Array.size_ofFn, nums'.2.1]; exact hi), Array.getElem_ofFn]

theorem permR {i : ℕ} (hi : i < 729) : permB 360 9 (T3R.T i) = true :=
  permB_of_pp (PP_pts T3R.ok r_perm i (by rw [nums'.2.1]; exact hi))

theorem entry_eq {e : ℕ} (he : e < 32) {r : ℕ} (pr : permB 360 9 r = true)
    (h : entK e r = true) :
    triEntryOK (triHArrs triData)[e]! (triYArrs triData)[e]! (triZArrs triData)[e]!
      (unpack 360 9 r) = true := by
  obtain ⟨eh, ph⟩ := hgen he
  obtain ⟨ey, py⟩ := ygen he
  obtain ⟨ez, pz⟩ := zgen he
  have pi : permB 360 9 (pinvS 360 9 (mask 9) (T3H e)) = true :=
    permB_of_pp (pp_of_permB hw9 ph).inv
  have pc := permB_pcomp hw9 ph (permB_pcomp hw9 pr pi)
  unfold entK at h
  rw [strictB_eq'] at h
  unfold triEntryOK
  rw [eh, ey, ez, conj_unpack' hw9 ph pr, comp_unpack' hw9 pc py, comp_unpack' hw9 py pc,
    comp_unpack' hw9 pc pz, comp_unpack' hw9 pz pc,
    eqA_unpack' hw9 (permB_pcomp hw9 pc py) (permB_pcomp hw9 py pc),
    eqA_unpack' hw9 (permB_pcomp hw9 pc pz) (permB_pcomp hw9 pz pc)]
  exact h

theorem point_eq {i : ℕ} (hi : i < 729) :
    triPointOK (triQCert triData) (triHArrs triData) (triYArrs triData) (triZArrs triData)
      (triRCert triData).pts[i]! = true := by
  have h := allN_spec pts i hi
  have pr := permR hi
  have p2 := permB_pcomp hw9 pr pr
  have p3 := permB_pcomp hw9 pr p2
  unfold triK at h
  unfold triPointOK
  rw [r_get i hi, comp_unpack' hw9 pr pr, comp_unpack' hw9 pr p2, idA_eq hw9,
    eqA_unpack' hw9 p3 permId,
    any_eqA_unpack' hw9 q_size q_get (fun j hj => permQ hj) pr]
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with (h | h) | ⟨hb, hent⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · right
    have he : T3W i < 32 := by simpa using hb
    rw [List.any_eq_true]
    exact ⟨T3W i, List.mem_range.2 (by rw [hsize]; exact he), entry_eq he pr hent⟩

theorem triCheck_true : triCheck triData = true := by
  unfold triCheck triCheck'
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨genAP.1, ?_⟩, by decide⟩, sizes.1⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, q_size⟩, ?_⟩, r_size⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [allLt_iff, genAP.1]
    intro k hk
    rw [genA k hk]
    exact validA_unpack (permA k hk)
  · rw [← Array.all_toList]
    exact lettersQ
  · exact lettersX
  · rw [← Array.all_toList]
    exact lettersH
  · rw [← Array.all_toList]
    exact lettersY
  · rw [← Array.all_toList]
    exact lettersZ
  · rw [sizes.2.2.1, sizes.2.1]
  · rw [sizes.2.2.2, sizes.2.1]
  · rw [qKeys_eq]
    exact q_enum
  · rw [rKeys_eq]
    exact r_enum
  · rw [allLt_iff, hsize]
    intro k hk
    rw [(hgen hk).1]
    exact validA_unpack (hgen hk).2
  · rw [allLt_iff, hsize]
    intro k hk
    obtain ⟨ey, py⟩ := ygen hk
    obtain ⟨ez, pz⟩ := zgen hk
    rw [ey, ez, comp_unpack' hw9 py pz, comp_unpack' hw9 pz py,
      eqA_unpack' hw9 (permB_pcomp hw9 py pz) (permB_pcomp hw9 pz py)]
    exact allN_spec ncomm k hk
  · rw [allLt_iff, r_size]
    intro i hi
    exact point_eq hi

end CertificateChecks.KernelO8.T3K

end
