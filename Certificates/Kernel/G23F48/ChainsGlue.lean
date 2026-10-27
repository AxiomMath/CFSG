module

public import Certificates.Kernel.G23F48.Chains
public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
public import CFSG.Certificates.Kernel.G23F48.WordBind

public section

set_option maxRecDepth 400000

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.HNOddCore CFSG.KC.Misc.ArrEnum

theorem getElem!_map_toArray {α : Type} {f : α → Array ℕ} {l : List α} {j : ℕ} (d : α)
    (hj : j < l.length) : (l.map f).toArray[j]! = f (l.getD j d) := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD, hj]

theorem letters_evA (word : List (Fin 4 × Bool)) :
    burnsideF48t_evA 728 burnsideF48t_g23LArr (burnsideF48t_g23LInv ()) word =
      unpack 728 10 (evP 728 10 LP LPI word) :=
  evA_eq_unpack (by norm_num) (by norm_num) (by decide +kernel)
    (fun i hi => allN_spec l_bind i hi) (fun i hi => allN_spec l_perm i hi) word

theorem s0Arr_eq : burnsideF48t_g23S0Arr () =
    (burnsideF48t_g23SW.map (burnsideF48t_evA 728 burnsideF48t_g23LArr
      (burnsideF48t_g23LInv ()))).toArray := rfl

theorem kArr_eq : burnsideF48t_g23KArr () =
    (burnsideF48t_g23KW.map (burnsideF48t_evA 728 burnsideF48t_g23LArr
      (burnsideF48t_g23LInv ()))).toArray := rfl

theorem s0Arr_get : (burnsideF48t_g23S0Arr ()).size = 3 ∧
    ∀ j < 3, (burnsideF48t_g23S0Arr ())[j]! = unpack 728 10 (S0C.S j) := by
  have hl : burnsideF48t_g23SW.length = 3 := by simp [burnsideF48t_g23SW]
  refine ⟨by rw [s0Arr_eq, List.size_toArray, List.length_map, hl], fun j hj => ?_⟩
  rw [s0Arr_eq, getElem!_map_toArray [] (by omega), letters_evA,
    Nat.eq_of_beq_eq_true (allN_spec s0_words j hj)]

theorem kArr_get : (burnsideF48t_g23KArr ()).size = 2 ∧
    ∀ j < 2, (burnsideF48t_g23KArr ())[j]! = unpack 728 10 (KCh.S j) := by
  have hl : burnsideF48t_g23KW.length = 2 := by simp [burnsideF48t_g23KW]
  refine ⟨by rw [kArr_eq, List.size_toArray, List.length_map, hl], fun j hj => ?_⟩
  rw [kArr_eq, getElem!_map_toArray [] (by omega), letters_evA,
    Nat.eq_of_beq_eq_true (allN_spec k_words j hj)]

theorem arrGen_words_le {W : List (List (Fin 4 × Bool))} {B : Subgroup (Equiv.Perm (Fin 728))}
    {σ : Fin 4 → Equiv.Perm (Fin 728)}
    (h : burnsideF48t_RecL 728 burnsideF48t_g23LArr (burnsideF48t_g23LInv ()) σ)
    (hB : σ 0 ∈ B ∧ σ 1 ∈ B) (hW : ∀ w ∈ W, ∀ l ∈ w, l.1.val < 2) :
    arrGen 728 (W.map (burnsideF48t_evA 728 burnsideF48t_g23LArr
      (burnsideF48t_g23LInv ()))).toArray ≤ B := by
  rw [arrGen, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < W.length := by simpa using hk
  rw [getElem!_map_toArray [] hk',
    CFSG.Sporadic.HNOddCore.permOfArr_eq_of_prep (burnsideF48t_prep_evA h _)]
  have hmem : W.getD k [] ∈ W := by
    rw [List.getD_eq_getElem _ _ hk']
    exact List.getElem_mem hk'
  refine burnsideF48s_ev_mem _ _ fun l hl => ?_
  obtain ⟨⟨v, hv4⟩, b⟩ := l
  have hv : v < 2 := hW _ hmem _ hl
  interval_cases v
  · exact hB.1
  · exact hB.2

theorem S0_le {B : Subgroup (Equiv.Perm (Fin 728))} {σ : Fin 4 → Equiv.Perm (Fin 728)}
    (h : burnsideF48t_RecL 728 burnsideF48t_g23LArr (burnsideF48t_g23LInv ()) σ)
    (hB : σ 0 ∈ B ∧ σ 1 ∈ B) : arrGen 728 (burnsideF48t_g23S0Arr ()) ≤ B := by
  rw [s0Arr_eq]
  exact arrGen_words_le h hB (by decide)

theorem K_le {B : Subgroup (Equiv.Perm (Fin 728))} {σ : Fin 4 → Equiv.Perm (Fin 728)}
    (h : burnsideF48t_RecL 728 burnsideF48t_g23LArr (burnsideF48t_g23LInv ()) σ)
    (hB : σ 0 ∈ B ∧ σ 1 ∈ B) : arrGen 728 (burnsideF48t_g23KArr ()) ≤ B := by
  rw [kArr_eq]
  exact arrGen_words_le h hB (by decide)

theorem chainS0_ok : burnsideF48t_g23ChainS0OK () = true :=
  chainCheck_of s0Arr_get (by decide +kernel) (by decide +kernel)
    (by simp only [s0D, Array.toArray_toList]) (by norm_num)
    ⟨by decide +kernel, fun t ht => (Nat.eq_of_beq_eq_true (allN_spec s0_base t ht)).symm⟩
    S0C.head S0C.hl (by decide +kernel) S0C.hs s0_perm s0_sizes

theorem chainK_ok : burnsideF48t_g23ChainKOK () = true :=
  chainCheck_of kArr_get (by decide +kernel) (by decide +kernel)
    (by simp only [kD, Array.toArray_toList]) (by norm_num)
    ⟨by decide +kernel, fun t ht => (Nat.eq_of_beq_eq_true (allN_spec k_base t ht)).symm⟩
    KCh.head KCh.hl (by decide +kernel) KCh.hs k_perm k_sizes

theorem card_S0 : Nat.card (arrGen 728 (burnsideF48t_g23S0Arr ())) = 729 := by
  rw [card_arrGen_of_chainCheck (by norm_num) (by decide) chainS0_ok]
  rfl

theorem card_K : Nat.card (arrGen 728 (burnsideF48t_g23KArr ())) = 4 := by
  rw [card_arrGen_of_chainCheck (by norm_num) (by decide) chainK_ok]
  rfl

end CFSG.KC.G23F48

end
