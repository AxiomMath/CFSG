module

public import Certificates.Kernel.SporSch.Ly.SevA
public import Certificates.Kernel.SporSch.Ly.SevV
public import CFSG.Certificates.Kernel.SporSch.LySeven7Sound
public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Certificates.Kernel.Spor.Loops
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.UInt.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.LyMatSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LySvD

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySev
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native
open CertificateChecks.KernelSporSch
open CFSG.Sporadic.Th.Native (allIn)

@[expose] noncomputable def lvV (i : Nat) : Array (Array Nat) :=
  ((hLevelGens.getD i []).map fun k => LySv.VALS.getD k (id7 ())).toArray

@[expose] noncomputable def VP (k : Nat) : Nat := pk49 (LySv.VALS[k]!)

@[expose] noncomputable def RAP (j : Nat) : Nat := pk49 (LySv.RA[j]!)

@[expose] noncomputable def dagStep (k : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun a bc => Prod.rec (motive := fun _ => Bool) (fun b c =>
    bIf(Nat.beq a 0, Nat.beq (VP k) (RAP b), bIf(Nat.beq a 1, Nat.beq (mul7K (VP b) (VP k)) id7K,
      Nat.beq (VP k) (mul7K (VP b) (VP c))))) bc) (hDag[k]!)

theorem gens5 : ∀ k < hDag.size, hDag[k]!.1 = 0 → hDag[k]!.2.1 < 5 := by decide +kernel

theorem dagSz : (LySv.VALS.size == hDag.size) = true := by decide +kernel

theorem hsz : hDag.size = 92 := by decide +kernel

theorem dagStr : (allIn 0 hDag.size fun k => hDag[k]!.1 == 0 ||
    (hDag[k]!.2.1 < k && (hDag[k]!.1 == 1 || hDag[k]!.2.2 < k))) = true := by decide +kernel

theorem fix1 : levelFixOK (lvV 1) 1 = true := by decide +kernel

theorem fix2 : levelFixOK (lvV 2) 2 = true := by decide +kernel

@[expose] noncomputable def is49 (a : Array Nat) (X : Nat) : Bool :=
  bAnd(Nat.beq a.size 49, allN 49 (fun t => Nat.beq (a[t]!) (d3 X t)))

theorem dec49_of {a : Array Nat} {X : Nat} (h : is49 a X = true) : a = dec49 X := by
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  have hs := Nat.eq_of_beq_eq_true h1
  apply Array.ext (by rw [hs]; simp [dec49])
  intro t ht _
  rw [hs] at ht
  rw [← getElem!_pos a t (by omega), Nat.eq_of_beq_eq_true (allN_spec h2 t ht)]
  simp [dec49]

theorem idOK : is49 (id7 ()) id7K = true := by quickRfl

theorem id7_eq : id7 () = dec49 id7K := dec49_of idOK

theorem vpOK : allN 92 (fun k => bAnd(is49 (LySv.VALS[k]!) (VP k), red49 (VP k))) = true := by
  quickRfl

theorem raOK : allN 5 (fun j => bAnd(is49 (LySv.RA[j]!) (RAP j), red49 (RAP j))) = true := by
  quickRfl

theorem dagK : allN 92 dagStep = true := by quickRfl

theorem vals_get {k : Nat} (hk : k < 92) : LySv.VALS[k]! = dec49 (VP k) :=
  dec49_of ((CFSG.KS.bAnd_iff _ _).1 (allN_spec vpOK k hk)).1

theorem red_vp {k : Nat} (hk : k < 92) : red49 (VP k) = true :=
  ((CFSG.KS.bAnd_iff _ _).1 (allN_spec vpOK k hk)).2

theorem ra_get {j : Nat} (hj : j < 5) : LySv.RA[j]! = dec49 (RAP j) :=
  dec49_of ((CFSG.KS.bAnd_iff _ _).1 (allN_spec raOK j hj)).1

theorem red_ra {j : Nat} (hj : j < 5) : red49 (RAP j) = true :=
  ((CFSG.KS.bAnd_iff _ _).1 (allN_spec raOK j hj)).2

theorem vals_getD {k : Nat} (hk : k < 92) (d : Array Nat) : LySv.VALS.getD k d = dec49 (VP k) := by
  have hs : LySv.VALS.size = 92 := by decide +kernel
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some,
    ← getElem!_pos LySv.VALS k (by omega), vals_get hk]

@[expose] def stepv (g : Nat → Array Nat) (vals : Array (Array Nat)) (e : Nat × Nat × Nat) :
    Array Nat :=
  if e.1 = 0 then g e.2.1 else if e.1 = 1 then inv7 (vals.getD e.2.1 (id7 ()))
    else mul7 (vals.getD e.2.1 (id7 ())) (vals.getD e.2.2 (id7 ()))

theorem str_of (k : Nat) (hk : k < hDag.size) (h0 : hDag[k]!.1 ≠ 0) :
    hDag[k]!.2.1 < k ∧ (hDag[k]!.1 ≠ 1 → hDag[k]!.2.2 < k) := by
  have := (CFSG.Sporadic.Th.allIn_eq_true.1 dagStr) k (Nat.zero_le _) hk
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with h | ⟨h1, h2⟩
  · exact absurd h h0
  · exact ⟨h1, fun h3 => h2.resolve_left h3⟩

theorem loc (k : Nat) (hk : k < hDag.size) :
    LySv.VALS[k]! = stepv (fun j => LySv.RA[j]!) LySv.VALS hDag[k]! := by
  have hk' : k < 92 := by rw [hsz] at hk; exact hk
  have d := allN_spec dagK k hk'
  unfold dagStep at d
  unfold stepv
  have hs := str_of k hk
  have hb5 := gens5 k hk
  generalize he : hDag[k]! = e at d hs hb5
  obtain ⟨a, b, c⟩ := e
  dsimp only at hs hb5 ⊢
  rcases a with _ | _ | a
  · have d0 : Nat.beq (VP k) (RAP b) = true := d
    rw [ite_eq_left rfl, vals_get hk', ra_get (hb5 rfl)]
    exact congrArg dec49 (Nat.eq_of_beq_eq_true d0)
  · have d1 : Nat.beq (mul7K (VP b) (VP k)) id7K = true := d
    have hb := (hs (by decide)).1
    rw [ite_eq_right (by decide), ite_eq_left rfl, vals_getD (by omega), vals_get hk',
      inv7_eq (red_vp (by omega)) (red_vp hk') (Nat.eq_of_beq_eq_true d1)]
  · have d2 : Nat.beq (VP k) (mul7K (VP b) (VP c)) = true := d
    obtain ⟨hb, hc⟩ := hs (by omega)
    have hc' := hc (by omega)
    rw [ite_eq_right (by omega), ite_eq_right (by omega), vals_getD (by omega), vals_getD (by omega),
      vals_get hk', mul7_eq]
    exact congrArg dec49 (Nat.eq_of_beq_eq_true d2)

theorem dagLoc : dagLocalOK (fun j => LySv.RA[j]!) LySv.VALS = true := by
  unfold dagLocalOK
  rw [CFSG.Sporadic.Th.allIn_eq_true]
  intro k _ hk
  have e := loc k hk
  unfold stepv at e
  simp only []
  rw [← e]
  exact beq_self_eq_true _

theorem inv_step (k : Nat) (hk : k < 92) (h1 : hDag[k]!.1 = 1) :
    mul7K (VP hDag[k]!.2.1) (VP k) = id7K := by
  have d := allN_spec dagK k hk
  unfold dagStep at d
  generalize he : hDag[k]! = e at d h1 ⊢
  obtain ⟨a, b, c⟩ := e
  dsimp only at h1 ⊢
  subst h1
  have d1 : Nat.beq (mul7K (VP b) (VP k)) id7K = true := d
  exact Nat.eq_of_beq_eq_true d1

theorem dagInv : dagInvOK LySv.VALS = true := by
  unfold dagInvOK
  rw [CFSG.Sporadic.Th.allIn_eq_true]
  intro k _ hk
  have hk' : k < 92 := by rw [hsz] at hk; exact hk
  simp only []
  by_cases h1 : hDag[k]!.1 = 1
  · have hb := (str_of k hk (by omega)).1
    rw [vals_getD (by omega), vals_get hk', mul7_eq, inv_step k hk' h1, id7_eq]
    simp
  · simp [h1]

@[expose] noncomputable def RAg (j : Nat) : Array Nat := LySv.RA[j]!

@[expose] noncomputable def stepF (vals : Array (Array Nat)) (e : Nat × Nat × Nat) : Array (Array Nat) :=
  vals.push (stepv RAg vals e)

theorem getD_of {A : Array (Array Nat)} {j : Nat} (h : j < A.size) (d : Array Nat) :
    A.getD j d = A[j]! := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some,
    getElem!_pos A j h]

theorem dag_eq : dagArr RAg = LySv.VALS := by
  have hs : LySv.VALS.size = 92 := by decide +kernel
  have hl : hDag.toList.length = 92 := by rw [Array.length_toList, hsz]
  have hdef : dagArr RAg = hDag.toList.foldl stepF #[] := by
    unfold dagArr stepF stepv
    rw [Array.foldl_toList]
  have key : ∀ n, n ≤ 92 → ((hDag.toList.take n).foldl stepF #[]).size = n ∧
      ∀ i < n, ((hDag.toList.take n).foldl stepF #[])[i]! = LySv.VALS[i]! := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hn' : n < hDag.size := by rw [hsz]; omega
      have ht : hDag.toList.take (n + 1) = hDag.toList.take n ++ [hDag[n]!] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), getElem!_pos hDag n hn']
        simp
      rw [ht, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (hDag.toList.take n).foldl stepF #[] = A at h1 h2
      have hstep : stepv RAg A hDag[n]! = LySv.VALS[n]! := by
        rw [loc n hn']
        unfold stepv
        by_cases h0 : hDag[n]!.1 = 0
        · rw [ite_eq_left h0, ite_eq_left h0]
          rfl
        · have hb := (str_of n hn' h0).1
          have eb : ∀ d, A.getD hDag[n]!.2.1 d = LySv.VALS.getD hDag[n]!.2.1 d := fun d => by
            rw [getD_of (A := A) (by omega), getD_of (A := LySv.VALS) (by omega), h2 _ hb]
          rw [ite_eq_right h0, ite_eq_right h0, eb]
          by_cases h1' : hDag[n]!.1 = 1
          · rw [ite_eq_left h1', ite_eq_left h1']
          · have hc := (str_of n hn' h0).2 h1'
            have ec : ∀ d, A.getD hDag[n]!.2.2 d = LySv.VALS.getD hDag[n]!.2.2 d := fun d => by
              rw [getD_of (A := A) (by omega), getD_of (A := LySv.VALS) (by omega), h2 _ hc]
            rw [ite_eq_right h1', ite_eq_right h1', ec]
      unfold stepF
      refine ⟨by rw [Array.size_push, h1], fun i hi => ?_⟩
      rcases Nat.lt_or_ge i n with hin | hin
      · rw [getElem!_pos _ i (by rw [Array.size_push]; omega), Array.getElem_push_lt (by omega),
          ← getElem!_pos A i (by omega), h2 i hin]
      · have : i = n := by omega
        subst this
        rw [getElem!_pos _ i (by rw [Array.size_push]; omega)]
        simp only [Array.getElem_push, h1, lt_irrefl, dite_false]
        exact hstep
  obtain ⟨k1, k2⟩ := key 92 le_rfl
  rw [List.take_of_length_le (by omega)] at k1 k2
  rw [hdef]
  apply Array.ext (by rw [k1, hs])
  intro i hi1 hi2
  rw [k1] at hi1
  rw [← getElem!_pos _ i (by rw [k1]; exact hi1), ← getElem!_pos LySv.VALS i (by omega)]
  exact k2 i hi1

end CertificateChecks.KernelSporSch.LySvD

end
