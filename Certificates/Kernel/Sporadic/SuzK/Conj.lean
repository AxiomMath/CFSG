module

public import Certificates.Kernel.Sporadic.SuzK.Keys
import Certificates.Kernel.Sporadic.SuzK.TreeK
import CFSG.Certificates.Kernel.Spor.PChainSound
import CFSG.Certificates.Kernel.Spor.TabWords
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.F3.Native CFSG.KS.F3L CFSG.Sporadic.Suz.Native CFSG.KC.Enum CFSG.KS.PEnum
  CFSG.Sporadic.Th.Native CFSG.KS.Raw.Orb

theorem foldl_indexW (keys : Array (Array W))
    (hinj : ∀ i < keys.size, ∀ j < keys.size, keys[i]! = keys[j]! → i = j) (d : Nat) :
    ∀ n ≤ keys.size, ∀ k < n,
      ((List.range n).foldl (fun m i => m.insert keys[i]! i)
        (∅ : Std.HashMap (Array W) Nat)).getD keys[k]! d = k := by
  intro n
  induction n with
  | zero => intro _ k hk; omega
  | succ n ih =>
    intro hn k hk
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Std.HashMap.getD_insert]
    by_cases hkn : k = n
    · subst hkn
      simp
    · have hne : (keys[n]! == keys[k]!) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        exact hkn (hinj n (by omega) k (by omega) e).symm
      rw [hne]
      exact ih (by omega) k (by omega)

theorem indexOfW_getD {keys : Array (Array W)}
    (hinj : ∀ i < keys.size, ∀ j < keys.size, keys[i]! = keys[j]! → i = j) {k : Nat}
    (hk : k < keys.size) : (indexOfW keys).getD keys[k]! keys.size = k :=
  foldl_indexW keys hinj keys.size keys.size (Nat.le_refl _) k hk

theorem keyW_size (k : Nat) : (keyW k).size = 64 := by
  unfold keyW
  rw [Array.size_map, unlane_size]

theorem eqW_self_of {X : Array W} (h : X.size = 64) : eqW 64 X X = true := by
  unfold eqW
  simp [h]

theorem W.wf_of_V {v : V} (hv : v.wf = true) (hp : v.p < 2 ^ 64) (hm : v.m < 2 ^ 64) :
    (ofV v).wf = true := by
  unfold W.wf
  rw [beq_iff_eq]
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_and]
  have h1 : (ofV v).p.toNat = v.p := by
    simp only [ofV, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hp]
  have h2 : (ofV v).m.toNat = v.m := by
    simp only [ofV, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hm]
  rw [h1, h2]
  unfold V.wf at hv
  rw [beq_iff_eq] at hv
  rw [hv]
  rfl

theorem canonW_keyW {k : Nat} (hk : k < 22880) : canonW (keyW k) = true := by
  have hall : ∀ v ∈ unlane 64 (laneK k), (ofV v).wf = true := by
    intro v hv
    obtain ⟨hp, hm⟩ := mem_unlane_lt hv
    unfold unlane at hv
    rw [Array.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact W.wf_of_V (blk_wf 64 (laneK_canon hk) i.val) hp hm
  unfold canonW
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨keyW_size k, fun i hi => ?_⟩
  simp only [keyW, Array.getElem_map]
  exact hall _ (Array.getElem_mem _)

theorem tree_pt {k : ℕ} (hk : k < 22880) (hk0 : k ≠ 0) : r32 PA k < k ∧
    ((r32 LB k = 1 ∧ r32 AL (r32 PA k) = k) ∨ (r32 LB k = 2 ∧ r32 BE (r32 PA k) = k)) := by
  have h0 := tree_ok
  unfold trK at h0
  have h := allN_iff.1 h0 k hk
  unfold trAt at h
  have hb : k.beq 0 = false := by
    cases e : k.beq 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hk0
  rw [CFSG.KS.Raw.Orb.bIf_eq, hb, if_neg Bool.false_ne_true, CFSG.KS.Raw.Orb.strictB_eq,
    CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, CFSG.KS.Raw.Orb.bIf_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simpa [Nat.blt_eq] using h1, ?_⟩
  cases e : Nat.beq (r32 LB k) 1
  · rw [e, if_neg Bool.false_ne_true, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h2
    exact Or.inr ⟨Nat.eq_of_beq_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2⟩
  · rw [e, if_pos rfl] at h2
    exact Or.inl ⟨Nat.eq_of_beq_eq_true e, Nat.eq_of_beq_eq_true h2⟩

theorem tree_conj {k : ℕ} (hk : k < 22880) : (k == 0 || (decide (ap orbLit.par k < k) &&
    ((ap orbLit.lab k == 1 && ap orbLit.alpha (ap orbLit.par k) == k) ||
      (ap orbLit.lab k == 2 && ap orbLit.beta (ap orbLit.par k) == k)))) = true := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rfl
  obtain ⟨hp, hl⟩ := tree_pt hk (by omega)
  have ep : ap orbLit.par k = r32 PA k := ap_tabOf PA hk
  have el : ap orbLit.lab k = r32 LB k := ap_tabOf LB hk
  have ea : ap orbLit.alpha (r32 PA k) = r32 AL (r32 PA k) := ap_tabOf AL (by omega)
  have eb : ap orbLit.beta (r32 PA k) = r32 BE (r32 PA k) := ap_tabOf BE (by omega)
  rw [ep, el, ea, eb]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact Or.inr ⟨hp, hl⟩

theorem alpha_ap {x : Nat} (hx : x < 22880) : ap orbLit.alpha x = r32 AL x := ap_tabOf AL hx

theorem beta_ap {x : Nat} (hx : x < 22880) : ap orbLit.beta x = r32 BE x := ap_tabOf BE hx

theorem inj_keys : ∀ i < orbLit.keys.size, ∀ j < orbLit.keys.size,
    orbLit.keys[i]! = orbLit.keys[j]! → i = j := by
  intro i hi j hj e
  rw [keys_size] at hi hj
  rw [keys_get hi, keys_get hj] at e
  exact keyW_inj hi hj e

theorem check_atW {k : Nat} (hk : k < 22880) :
    conjCheckAtW 64 (wA ()) (wA ()) (wB ()) (wBi ()) orbLit
      (fun X => (indexOfW orbLit.keys).getD X orbLit.keys.size) k = true := by
  have hs := keys_size
  have ha : ap orbLit.alpha k = r32 AL k := ap_tabOf AL hk
  have hb : ap orbLit.beta k = r32 BE k := ap_tabOf BE hk
  have ha' : ap orbLit.alpha k < orbLit.keys.size := by rw [ha, hs]; exact al_lt hk
  have hb' : ap orbLit.beta k < orbLit.keys.size := by rw [hb, hs]; exact be_lt hk
  have hpos : (indexOfW orbLit.keys).getD orbLit.keys[k]! orbLit.keys.size = k :=
    indexOfW_getD inj_keys (by omega)
  have c1 : canonW orbLit.keys[k]! = true := by rw [keys_get hk]; exact canonW_keyW hk
  have e1 : eqW 64 (conjW 64 (wA ()) (wA ()) orbLit.keys[k]!) orbLit.keys[ap orbLit.alpha k]! =
      true := by
    rw [ha, keys_get hk, keys_get (al_lt hk), hA_key hk]
    exact eqW_self_of (keyW_size _)
  have e2 : eqW 64 (conjW 64 (wB ()) (wBi ()) orbLit.keys[k]!) orbLit.keys[ap orbLit.beta k]! =
      true := by
    rw [hb, keys_get hk, keys_get (be_lt hk), hB_key hk]
    exact eqW_self_of (keyW_size _)
  have ht := tree_conj hk
  unfold conjCheckAtW
  dsimp only
  rw [c1, hpos, e1, e2, ht, decide_eq_true ha', decide_eq_true hb']
  simp

theorem conj_okW (chunks : Nat) :
    conjOrbitOKW 64 (wRoot ()) (wA ()) (wA ()) (wB ()) (wBi ()) orbLit chunks = true := by
  have hs := keys_size
  unfold conjOrbitOKW
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨by rw [hs]; norm_num, by rw [hs]; norm_num⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [keys_get (by norm_num), root_key, ← root_key]
    exact eqW_self_of (keyW_size 0)
  · unfold CFSG.Sporadic.Th.Native.invoOK
    rw [CFSG.KS.TW.allIn_iff]
    intro i hi
    rw [hs] at hi
    rw [alpha_ap hi, alpha_ap (al_lt hi), alpha_inv hi, beq_self_eq_true]
  · unfold CFSG.Sporadic.Th.Native.order3OK
    rw [CFSG.KS.TW.allIn_iff]
    intro i hi
    rw [hs] at hi
    have h1 := be_lt hi
    rw [beta_ap hi, beta_ap h1, beta_ap (be_lt h1), beta_ord hi, beq_self_eq_true]
  · exact CFSG.KS.PC.parAll_of fun k hk => check_atW (by rwa [hs] at hk)

end CertificateChecks.KernelSpor.SuzK

end
