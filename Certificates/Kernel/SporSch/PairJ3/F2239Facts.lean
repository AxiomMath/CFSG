module

public import Certificates.Kernel.SporSch.PairJ3.F2239Sep
public import Certificates.Kernel.SporSch.PairJ3.FormsLe
public import Certificates.Kernel.SporSch.PairJ3.Check2236
public import Certificates.Kernel.Sporadic.J3K.Final
public import Certificates.Kernel.J4Q.Mat
public import CFSG.Certificates.Kernel.SporSch.J3F80Sound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Schreier.PairJ3FaithfulCheckInputs
public meta import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.J3.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CertificateChecks.KernelSporSch.F2239

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS CFSG.KS.SporSch CFSG.KS.SporSch.J3F CFSG.KD.J3F
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairJ3 CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSpor.J3K

set_option maxRecDepth 100000

theorem hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6 := CertificateChecks.KernelJ4Q.hK

theorem andR {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem slices_all {k S : Nat} {f : Nat → Bool} (h : ∀ s < S, allBlk (Nat.mul k s) f k = true) :
    ∀ j < k * S, f j = true := by
  intro j hj
  have hk : 0 < k := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hj
  have hs : j / k < S := by
    rw [Nat.div_lt_iff_lt_mul hk]
    rw [Nat.mul_comm] at hj
    exact hj
  have := allBlk_spec (h (j / k) hs) (j % k) (Nat.mod_lt _ hk)
  rwa [show Nat.add (Nat.mul k (j / k)) (j % k) = j from Nat.div_add_mod j k] at this

theorem chars_eq : PJ3FT.chars = chunks.flatten := by
  delta PJ3FT.chars chunks
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

theorem hasc : ∀ c ∈ chunks, le70K c = true := by
  simp only [chunks, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  exact ⟨PJ3FT.ok0, PJ3FT.ok1, PJ3FT.ok2, PJ3FT.ok3, PJ3FT.ok4, PJ3FT.ok5, PJ3FT.ok6, PJ3FT.ok7,
    PJ3FT.ok8, PJ3FT.ok9, PJ3FT.ok10, PJ3FT.ok11, PJ3FT.ok12, PJ3FT.ok13, PJ3FT.ok14, PJ3FT.ok15,
    PJ3FT.ok16, PJ3FT.ok17, PJ3FT.ok18, PJ3FT.ok19, PJ3FT.ok20, PJ3FT.ok21, PJ3FT.ok22, PJ3FT.ok23,
    PJ3FT.ok24, PJ3FT.ok25, PJ3FT.ok26, PJ3FT.ok27, PJ3FT.ok28, PJ3FT.ok29, PJ3FT.ok30, PJ3FT.ok31,
    PJ3FT.ok32, PJ3FT.ok33, PJ3FT.ok34, PJ3FT.ok35, PJ3FT.ok36, PJ3FT.ok37⟩

theorem hF : ∀ r < 6156, hexAt j3FormsHex.toUTF8 (810 * r) 810 = FW r := by
  have hlen : chunks.length = 38 := rfl
  have h := words_sound (k := 162) (F := FW) hasc fun j hj =>
    slices_all (k := 1) (S := 38) FWC.all j (by rw [hlen] at hj; omega)
  rw [PJ3FT.eq, chars_eq]
  intro r hr
  exact h r (by rw [hlen]; omega)

theorem hInv : j3InvWord = INVW := by
  obtain ⟨h1, h2⟩ := andR (a := le70K PJ3I.c0) (b := wordsK (fun _ => INVW) 1 0 PJ3I.c0) invC
  have h := words_sound (cs := [PJ3I.c0]) (k := 1) (F := fun _ => INVW)
    (by simpa using h1) (fun j hj => by
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      exact h2) 0 (by simp)
  rw [j3InvWord, PJ3I.eq]
  simpa [PJ3I.chars] using h

theorem fF_lt {r : Nat} (h : fF r = true) : FW r < 2 ^ 3240 := by
  have h' : formsF c rm t0 t1 t2 t3 t4 t5 t6 usK dgK FW (PJ3.S 0) (PJ3.S 1) A1 A1T A2 A2T r = true :=
    h
  unfold formsF at h'
  rw [strictB_eq'] at h'
  have := (andR h').1
  have e : Nat.shiftLeft (nat_lit 1) (nat_lit 3240) = 2 ^ 3240 := by norm_num [Nat.shiftLeft_eq]
  rw [e] at this
  simpa [Nat.blt_eq] using this

theorem fF_all : ∀ r < 6156, fF r = true := slices_all (k := 162) (S := 38) FFS.all

open Certificates in
open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairJ3 in
open CFSG.Sporadic.Schreier.PairF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native in
theorem facts : (formsCheckWith j3FormsHex.toUTF8 j3StrongArrs rowsA1 rowsA2 = true)
    ∧ (PairNative.strictInc (sortedWords j3FormsHex.toUTF8) = true)
    ∧ (pullOKZ 80 rowsA1 j3InvWord j3InvWord = true ∧ pullOKZ 80 rowsA2 j3InvWord j3InvWord = true ∧
      mulRows 80 BInv BRows = idRows 80
    )
    ∧ (sepCheckWith TRows = true) := by
  have hA1 : rowsA1 = RAL.toArray := rowsA_D
  have hA2 : rowsA2 = RBL.toArray := rowsB_D
  obtain ⟨r1, r2⟩ := andR (a := rows80K RAL) (b := rows80K RBL) rows
  have p2 := pull1
  have p3 := pull2
  have hlt : INVW < 2 ^ 3240 := by
    have p1 := invLt
    have e : Nat.shiftLeft 1 3240 = 2 ^ 3240 := by norm_num [Nat.shiftLeft_eq]
    rw [e] at p1
    simpa [Nat.blt_eq] using p1
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hA1, hA2]
    exact forms_sound hK hF (PJ3Cert.arr_eq 0 (by norm_num)) (PJ3Cert.arr_eq 1 (by norm_num)) r1 r2
      fF_all
  · exact sort_sound hF sort
  · rw [hA1, hInv]
    exact pull_sound hK r1 hlt p2
  · rw [hA2, hInv]
    exact pull_sound hK r2 hlt p3
  · rw [BInv, BRows, hInv]
    exact binv_sound hK hlt binv
  · have hw : ∀ r : Fin 4, j3FormWord r.val = [FW 0, FW 1, FW 2, FW 3].getD r.val 0 := by
      intro r
      fin_cases r
      · exact hF 0 (by norm_num)
      · exact hF 1 (by norm_num)
      · exact hF 2 (by norm_num)
      · exact hF 3 (by norm_num)
    have hT : TRows = Array.ofFn fun r : Fin 4 =>
        CFSG.Sporadic.SmallF2.Native.mulRows 80 (PairF2.invRowsF2 80 (PairF2.polarRowsZ 80 INVW))
          (PairF2.polarRowsZ 80 ([FW 0, FW 1, FW 2, FW 3].getD r.val 0)) := by
      unfold TRows BInv BRows
      rw [hInv]
      exact congrArg (Array.ofFn (n := 4)) (funext fun r => by rw [hw r])
    have hz4 : ∀ z ∈ [FW 0, FW 1, FW 2, FW 3], z < 2 ^ 3240 := by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with h | h | h | h <;> rw [h]
      · exact fF_lt (fF_all 0 (by norm_num))
      · exact fF_lt (fF_all 1 (by norm_num))
      · exact fF_lt (fF_all 2 (by norm_num))
      · exact fF_lt (fF_all 3 (by norm_num))
    have hlen : [FW 0, FW 1, FW 2, FW 3].length = 4 := List.length_cons ▸ rfl
    have hsep := sep_sound (zB := INVW) (RB := RB) (SI := SI) (zs := [FW 0, FW 1, FW 2, FW 3]) hK
      hlen hlt hz4 prow sep
    rw [hT]
    exact hsep

end CertificateChecks.KernelSporSch.F2239

end
