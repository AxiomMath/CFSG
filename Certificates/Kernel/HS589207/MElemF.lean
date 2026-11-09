module

public import Certificates.Kernel.HS589207.M
public import CFSG.Certificates.Kernel.DcHSOutKSound
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KD.HS589207.MElemF

open CFSG.KC.DcK CFSG.KC.DcHSOutK CFSG.KC.Enum CFSG.Quasithin.H13.LocDbl.HSLoc

@[expose] noncomputable def rowEqF (a b : Nat) (g : Nat → Nat) : Bool :=
  allN 100 fun q => Nat.beq (fl a q) (g (fl b q))

theorem rowEqF_spec {a b : Nat} {g : Nat → Nat} (h : rowEqF a b g = true) :
    (List.range 100).map (CFSG.KC.LQT.PW.imgW 14 a) =
      ((List.range 100).map (CFSG.KC.LQT.PW.imgW 14 b)).map g := by
  rw [rowEqF, allN_eq', List.all_eq_true] at h
  rw [List.map_map]
  exact List.map_congr_left fun q hq => Nat.eq_of_beq_eq_true (h q hq)

@[expose] noncomputable def elemMF (G : Nat → Nat → Nat) (T : Nat → Nat) (k : Nat) : Bool :=
  (if k == 0 then (recK 11520 100 T).row 0 == B100 && (recK 11520 100 T).par 0 == 0 &&
      (recK 11520 100 T).lab 0 == 0 && (recK 11520 100 T).cnt 0 == 1
    else decide ((recK 11520 100 T).par k < k) && decide ((recK 11520 100 T).lab k < 2) &&
      rowEqF (T k) (T ((recK 11520 100 T).par k)) (G ((recK 11520 100 T).lab k))) &&
  (List.range 2).all (fun t => decide ((recK 11520 100 T).tgt k t < (recK 11520 100 T).N) &&
    rowEqF (T ((recK 11520 100 T).tgt k t)) (T k) (G t)) &&
  decide ((recK 11520 100 T).sig k < (recK 11520 100 T).N) &&
    (recK 11520 100 T).sinv ((recK 11520 100 T).sig k) == k &&
    decide ((recK 11520 100 T).sinv k < (recK 11520 100 T).N) &&
    (recK 11520 100 T).sig ((recK 11520 100 T).sinv k) == k &&
  (decide ((recK 11520 100 T).N ≤ k + 1) ||
    decide ((recK 11520 100 T).skey 100 B100.length k <
      (recK 11520 100 T).skey 100 B100.length (k + 1))) &&
  decide (k < (recK 11520 100 T).cnt k) &&
  replayRow (recK 11520 100 T) k (List.range 2) ((recK 11520 100 T).cnt k) ==
    some (if k + 1 < (recK 11520 100 T).N then (recK 11520 100 T).cnt (k + 1)
      else (recK 11520 100 T).N)

theorem elemK_of_elemMF {G : Nat → Nat → Nat} {T : Nat → Nat} {k : Nat}
    (h : elemMF G T k = true) : elemK 100 B100 G 2 (recK 11520 100 T) k = true := by
  unfold elemMF at h
  unfold elemK
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, fun t ht => ?_⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
  · by_cases hk : (k == 0) = true
    · rw [if_pos hk] at h1 ⊢
      exact h1
    · rw [if_neg hk] at h1 ⊢
      simp only [Bool.and_eq_true] at h1 ⊢
      obtain ⟨⟨h1a, h1b⟩, h1c⟩ := h1
      refine ⟨⟨h1a, h1b⟩, ?_⟩
      rw [beq_iff_eq]
      exact rowEqF_spec h1c
  · obtain ⟨h2a, h2b⟩ := h2 t ht
    refine ⟨h2a, ?_⟩
    rw [beq_iff_eq]
    exact (rowEqF_spec h2b).symm

theorem allBlk_ofM {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    have h2 : allBlk b f len = true := allBlk_ofM fun l hl => h l (Nat.lt_succ_of_lt hl)
    have h' : Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) =
        true := (CFSG.KS.bAnd_iff _ _).2 ⟨h len (Nat.lt_succ_self len), h2⟩
    exact h'

theorem allBlk_cat {b a c : Nat} {f : Nat → Bool} (h1 : allBlk b f a = true)
    (h2 : allBlk (b + a) f c = true) : allBlk b f (a + c) = true :=
  allBlk_ofM fun l hl => by
    rcases Nat.lt_or_ge l a with hla | hla
    · exact CFSG.KS.allBlk_spec h1 l hla
    · have := CFSG.KS.allBlk_spec h2 (l - a) (by omega)
      have e : Nat.add (b + a) (l - a) = Nat.add b l := by
        change b + a + (l - a) = b + l
        omega
      rwa [e] at this

theorem elemsK_of_blk {lo len : Nat} (h : allBlk lo (elemMF GM MR.TF) len = true) :
    elemsK 100 B100 GM 2 EM lo len = true := by
  unfold elemsK
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range'_1] at hk
  have := CFSG.KS.allBlk_spec h (k - lo) (by omega)
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rw [e] at this
  exact elemK_of_elemMF this

end CFSG.KD.HS589207.MElemF

end
