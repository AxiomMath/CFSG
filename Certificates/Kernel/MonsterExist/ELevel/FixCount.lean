module

public import CFSG.Monster.Tri.LeechModelFixInputs
public import Certificates.Kernel.MonsterExist.ELevel.Check
public import CFSG.Monster.Tri.LeechData

public section

set_option maxRecDepth 100000

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.ELevel

open CFSG.KC CFSG.KC.Loop CFSG.Monster CFSG.Monster.B CFSG.Monster.Existence
  CFSG.Monster.B.TwoA.Census CFSG.Monster.VisCert CertificateChecks.MonsterExist.ShortKey
  CFSG.Monster.Tri.Leech

theorem findAll_nodup (p : ℕ → Bool) :
    ∀ (n : ℕ) (acc : List ℕ), acc.Nodup → (∀ a ∈ acc, n ≤ a) → (findAll p n acc).Nodup
  | 0, acc, h, _ => h
  | n + 1, acc, h, hge => by
    refine findAll_nodup p n _ ?_ ?_
    · by_cases hp : p n = true
      · rw [if_pos hp]
        exact List.nodup_cons.2 ⟨fun hm => by have := hge n hm; omega, h⟩
      · rw [if_neg hp]
        exact h
    · intro a ha
      by_cases hp : p n = true
      · rw [if_pos hp] at ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact le_refl _
        · have := hge a ha
          omega
      · rw [if_neg hp] at ha
        have := hge a ha
        omega

theorem shortPacked_nodup : shortPacked.Nodup := by
  unfold shortPacked foundCodes
  refine List.Nodup.map_on (fun x hx y hy e => ?_)
    (findAll_nodup _ _ [] List.nodup_nil (fun a ha => absurd ha List.not_mem_nil))
  have hx' : x < 2 ^ 24 := by
    rcases (mem_findAll _ _ _).1 hx with ⟨h, -⟩ | h
    · exact h
    · exact absurd h List.not_mem_nil
  have hy' : y < 2 ^ 24 := by
    rcases (mem_findAll _ _ _).1 hy with ⟨h, -⟩ | h
    · exact h
    · exact absurd h List.not_mem_nil
  rw [← actRows_convRows_convInvRows hx', e, actRows_convRows_convInvRows hy']

theorem fixCountX_le_of {i TB DB TT sw nCV CV nCS CS : ℕ} {FB : List ℕ}
    (h1 : PermArr (cosetArr i) = true) (h2 : AutArr (cosetArr i)) (hb : BasisOK i TB DB)
    (htt : ttOK TB DB FB TT = true)
    (hpass : ∀ c < 8, passRange (passT TT sw nCV CV nCS CS) (512 * c) 512 = true)
    (hcv : CV < 2 ^ (25 * nCV) ∧ ∀ t < nCV, laneW 25 CV t < 2 ^ 24)
    (hcs : CS < 2 ^ (25 * nCS) ∧ ∀ t < nCS, laneW 25 CS t < 2 ^ 24) :
    fixCountX i ≤ nCV := by
  have hk : ∀ u, kapX (tT i) (tD i) u = kapL TB DB u := kapX_eq_kapL h1 h2 hb
  have hall := pass_all hpass
  unfold fixCountX
  dsimp only
  have hsub : shortPacked.filter (fun x => kapX (tT i) (tD i) x == x) ⊆
      (List.range nCV).map (laneW 25 CV) := by
    intro x hx
    rw [List.mem_filter] at hx
    obtain ⟨hx24, hm⟩ := mem_shortPacked_iff_memK.1 hx.1
    have hp := bucketAll_sound _ hall x ((memK_iff_mem bucket_ok hx24).1 hm)
    obtain ⟨t, ht, e⟩ :=
      (passT_spec htt hcv hcs hx24 hp).1 (by rw [← hk]; exact beq_iff_eq.1 hx.2)
    exact List.mem_map.2 ⟨t, List.mem_range.2 ht, e⟩
  have hl := ((shortPacked_nodup.filter _).subperm hsub).length_le
  rwa [List.length_map, List.length_range] at hl

theorem fixCountX_one : fixCountX 1 ≤ 2280 :=
  fixCountX_le_of perm1 aut1 basis1 tt1 (fun c hc => by
    interval_cases c
    exacts [pass1_0, pass1_1, pass1_2, pass1_3, pass1_4, pass1_5, pass1_6, pass1_7]) cv1 cs1

theorem fixCountX_two : fixCountX 2 ≤ 264 :=
  fixCountX_le_of perm2 aut2 basis2 tt2 (fun c hc => by
    interval_cases c
    exacts [pass2_0, pass2_1, pass2_2, pass2_3, pass2_4, pass2_5, pass2_6, pass2_7]) cv2 cs2

theorem fixCountX_six : fixCountX 6 ≤ 0 :=
  fixCountX_le_of (nCV := 0) (nCS := 0) (CV := 0) (CS := 0) perm6 aut6 basis6 tt6 (fun c hc => by
      interval_cases c
      exacts [pass6_0, pass6_1, pass6_2, pass6_3, pass6_4, pass6_5, pass6_6, pass6_7])
    ⟨by norm_num, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
    ⟨by norm_num, fun t ht => absurd ht (Nat.not_lt_zero t)⟩

theorem fixCountX_le_all : ∀ i ∈ ({1, 2, 6} : Finset ℕ), fixCountX i ≤ 4071 := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · exact fixCountX_one.trans (by norm_num)
  · exact fixCountX_two.trans (by norm_num)
  · exact fixCountX_six.trans (by norm_num)

end CertificateChecks.MonsterExist.ELevel

end
