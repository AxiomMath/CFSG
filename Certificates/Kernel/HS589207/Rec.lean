module

public import Certificates.Kernel.HS589207.M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK
import CFSG.Certificates.Kernel.Spor.RawOrbEval

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589207.Rec

open CFSG.KC.DcHSOutK CFSG.KC.BfsRecK CFSG.KC.Enum

@[expose] noncomputable def rTree (k : Nat) (P L : Nat → Nat) (stEq : Nat → Nat → Nat → Bool)
    (i : Nat) : Bool :=
  Nat.beq i 0 || (Nat.blt (P i) i && Nat.blt (L i) k && stEq (L i) (P i) i)

@[expose] noncomputable def rOrd (k cnt : Nat) (P L : Nat → Nat) (i : Nat) : Bool :=
  Nat.beq i 0 || !Nat.blt (i + 1) cnt || Nat.blt (k * P i + L i) (k * P (i + 1) + L (i + 1))

@[expose] noncomputable def rEdge (k cnt : Nat) (P L POS : Nat → Nat)
    (stEq : Nat → Nat → Nat → Bool) (e : Nat) : Bool :=
  Nat.blt (POS e) cnt && stEq (e % k) (e / k) (POS e) &&
    (Nat.beq (POS e) 0 || Nat.ble (k * P (POS e) + L (POS e)) e)

@[expose] noncomputable def rSig (cnt : Nat) (K sig sinv : Nat → Nat) (j : Nat) : Bool :=
  Nat.blt (sig j) cnt && Nat.beq (sinv (sig j)) j &&
    Nat.blt (sinv j) cnt && Nat.beq (sig (sinv j)) j &&
    (!Nat.blt (j + 1) cnt || Nat.blt (K (sig j)) (K (sig (j + 1))))

theorem recOK_eq (k cnt : Nat) (P L POS K sig sinv : Nat → Nat)
    (stEq : Nat → Nat → Nat → Bool) :
    recOK k cnt P L POS K sig sinv stEq = (Nat.beq (P 0) 0 && Nat.beq (L 0) 0 &&
      allN cnt (rTree k P L stEq) && allN cnt (rOrd k cnt P L) &&
      allN (k * cnt) (rEdge k cnt P L POS stEq) && allN cnt (rSig cnt K sig sinv)) := rfl

theorem blocks_all {f : Nat → Bool} (B N : Nat)
    (h : ∀ s < N, allN B (fun j => f (Nat.add (Nat.mul B s) j)) = true) :
    ∀ i < B * N, f i = true := by
  intro a ha
  have hB : 0 < B := Nat.pos_of_ne_zero fun h0 => by simp [h0] at ha
  have hs : a / B < N := (Nat.div_lt_iff_lt_mul hB).2 (by rwa [Nat.mul_comm] at ha)
  have := CFSG.KS.Raw.Orb.allN_iff.1 (h (a / B) hs) (a % B) (Nat.mod_lt a hB)
  change f (B * (a / B) + a % B) = true at this
  rwa [Nat.div_add_mod] at this

theorem recOK_of {k cnt : Nat} {P L POS K sig sinv : Nat → Nat} {stEq : Nat → Nat → Nat → Bool}
    (hP : Nat.beq (P 0) 0 = true) (hL : Nat.beq (L 0) 0 = true)
    (hT : ∀ i < cnt, rTree k P L stEq i = true) (hO : allN cnt (rOrd k cnt P L) = true)
    (hE : ∀ e < k * cnt, rEdge k cnt P L POS stEq e = true)
    (hS : ∀ j < cnt, rSig cnt K sig sinv j = true) :
    recOK k cnt P L POS K sig sinv stEq = true := by
  rw [recOK_eq]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨hP, hL⟩, CFSG.KS.Raw.Orb.allN_iff.2 hT⟩, hO⟩, CFSG.KS.Raw.Orb.allN_iff.2 hE⟩,
    CFSG.KS.Raw.Orb.allN_iff.2 hS⟩

theorem f_P : Nat.beq (FP 0) 0 = true := by quickRfl
theorem f_L : Nat.beq (FL 0) 0 = true := by quickRfl
theorem f_ord : allN 3850 (rOrd 4 3850 FP FL) = true := by quickRfl
theorem f_sig : allN 3850 (rSig 3850 (keyF FR.TF) Fsig Fsinv) = true := by quickRfl

theorem f_t0 : allN 1925 (fun j => rTree 4 FP FL (stF A FR.TF) (Nat.add (Nat.mul 1925 0) j)) = true := by
  quickRfl
theorem f_t1 : allN 1925 (fun j => rTree 4 FP FL (stF A FR.TF) (Nat.add (Nat.mul 1925 1) j)) = true := by
  quickRfl

theorem f_e0 : allN 1925
    (fun j => rEdge 4 3850 FP FL FPOS (stF A FR.TF) (Nat.add (Nat.mul 1925 0) j)) = true := by quickRfl
theorem f_e1 : allN 1925
    (fun j => rEdge 4 3850 FP FL FPOS (stF A FR.TF) (Nat.add (Nat.mul 1925 1) j)) = true := by quickRfl
theorem f_e2 : allN 1925
    (fun j => rEdge 4 3850 FP FL FPOS (stF A FR.TF) (Nat.add (Nat.mul 1925 2) j)) = true := by quickRfl
theorem f_e3 : allN 1925
    (fun j => rEdge 4 3850 FP FL FPOS (stF A FR.TF) (Nat.add (Nat.mul 1925 3) j)) = true := by quickRfl
theorem f_e4 : allN 1925
    (fun j => rEdge 4 3850 FP FL FPOS (stF A FR.TF) (Nat.add (Nat.mul 1925 4) j)) = true := by quickRfl
theorem f_e5 : allN 1925
    (fun j => rEdge 4 3850 FP FL FPOS (stF A FR.TF) (Nat.add (Nat.mul 1925 5) j)) = true := by quickRfl
theorem f_e6 : allN 1925
    (fun j => rEdge 4 3850 FP FL FPOS (stF A FR.TF) (Nat.add (Nat.mul 1925 6) j)) = true := by quickRfl
theorem f_e7 : allN 1925
    (fun j => rEdge 4 3850 FP FL FPOS (stF A FR.TF) (Nat.add (Nat.mul 1925 7) j)) = true := by quickRfl

theorem frec : recOK 4 3850 FP FL FPOS (keyF FR.TF) Fsig Fsinv (stF A FR.TF) = true :=
  recOK_of (k := 4) (cnt := 3850) (P := FP) (L := FL) (POS := FPOS) (K := keyF FR.TF) (sig := Fsig)
    (sinv := Fsinv) (stEq := stF A FR.TF) f_P f_L
    (blocks_all (f := rTree 4 FP FL (stF A FR.TF)) 1925 2 fun s hs => match s, hs with
      | 0, _ => f_t0 | 1, _ => f_t1 | _ + 2, h => absurd h (by omega))
    f_ord
    (blocks_all (f := rEdge 4 3850 FP FL FPOS (stF A FR.TF)) 1925 8 fun s hs => match s, hs with
      | 0, _ => f_e0 | 1, _ => f_e1 | 2, _ => f_e2 | 3, _ => f_e3
      | 4, _ => f_e4 | 5, _ => f_e5 | 6, _ => f_e6 | 7, _ => f_e7 | _ + 8, h => absurd h (by omega))
    (CFSG.KS.Raw.Orb.allN_iff.1 f_sig)

theorem fent : (allN 3850 (fun i => (setT FR.TF i).all fun x => Nat.blt x 100) &&
    setT FR.TF 0 == [0, 1, 5, 21, 39, 50, 53, 61]) = true := by
  quickRfl

theorem c_P : Nat.beq (CP 0) 0 = true := by quickRfl
theorem c_L : Nat.beq (CL 0) 0 = true := by quickRfl
theorem c_ord : allN 1100 (rOrd 4 1100 CP CL) = true := by quickRfl
theorem c_s0 : allN 550 (fun j => rSig 1100 (keyC CR.TF) Csig Csinv (Nat.add (Nat.mul 550 0) j)) = true := by
  quickRfl
theorem c_s1 : allN 550 (fun j => rSig 1100 (keyC CR.TF) Csig Csinv (Nat.add (Nat.mul 550 1) j)) = true := by
  quickRfl

theorem c_t0 : allN 275 (fun j => rTree 4 CP CL (stC A CR.TF) (Nat.add (Nat.mul 275 0) j)) = true := by
  quickRfl
theorem c_t1 : allN 275 (fun j => rTree 4 CP CL (stC A CR.TF) (Nat.add (Nat.mul 275 1) j)) = true := by
  quickRfl
theorem c_t2 : allN 275 (fun j => rTree 4 CP CL (stC A CR.TF) (Nat.add (Nat.mul 275 2) j)) = true := by
  quickRfl
theorem c_t3 : allN 275 (fun j => rTree 4 CP CL (stC A CR.TF) (Nat.add (Nat.mul 275 3) j)) = true := by
  quickRfl

theorem c_e0 : allN 550
    (fun j => rEdge 4 1100 CP CL CPOS (stC A CR.TF) (Nat.add (Nat.mul 550 0) j)) = true := by quickRfl
theorem c_e1 : allN 550
    (fun j => rEdge 4 1100 CP CL CPOS (stC A CR.TF) (Nat.add (Nat.mul 550 1) j)) = true := by quickRfl
theorem c_e2 : allN 550
    (fun j => rEdge 4 1100 CP CL CPOS (stC A CR.TF) (Nat.add (Nat.mul 550 2) j)) = true := by quickRfl
theorem c_e3 : allN 550
    (fun j => rEdge 4 1100 CP CL CPOS (stC A CR.TF) (Nat.add (Nat.mul 550 3) j)) = true := by quickRfl
theorem c_e4 : allN 550
    (fun j => rEdge 4 1100 CP CL CPOS (stC A CR.TF) (Nat.add (Nat.mul 550 4) j)) = true := by quickRfl
theorem c_e5 : allN 550
    (fun j => rEdge 4 1100 CP CL CPOS (stC A CR.TF) (Nat.add (Nat.mul 550 5) j)) = true := by quickRfl
theorem c_e6 : allN 550
    (fun j => rEdge 4 1100 CP CL CPOS (stC A CR.TF) (Nat.add (Nat.mul 550 6) j)) = true := by quickRfl
theorem c_e7 : allN 550
    (fun j => rEdge 4 1100 CP CL CPOS (stC A CR.TF) (Nat.add (Nat.mul 550 7) j)) = true := by quickRfl

theorem crec : recOK 4 1100 CP CL CPOS (keyC CR.TF) Csig Csinv (stC A CR.TF) = true :=
  recOK_of (k := 4) (cnt := 1100) (P := CP) (L := CL) (POS := CPOS) (K := keyC CR.TF) (sig := Csig)
    (sinv := Csinv) (stEq := stC A CR.TF) c_P c_L
    (blocks_all (f := rTree 4 CP CL (stC A CR.TF)) 275 4 fun s hs => match s, hs with
      | 0, _ => c_t0 | 1, _ => c_t1 | 2, _ => c_t2 | 3, _ => c_t3 | _ + 4, h => absurd h (by omega))
    c_ord
    (blocks_all (f := rEdge 4 1100 CP CL CPOS (stC A CR.TF)) 550 8 fun s hs => match s, hs with
      | 0, _ => c_e0 | 1, _ => c_e1 | 2, _ => c_e2 | 3, _ => c_e3
      | 4, _ => c_e4 | 5, _ => c_e5 | 6, _ => c_e6 | 7, _ => c_e7 | _ + 8, h => absurd h (by omega))
    (blocks_all (f := rSig 1100 (keyC CR.TF) Csig Csinv) 550 2 fun s hs => match s, hs with
      | 0, _ => c_s0 | 1, _ => c_s1 | _ + 2, h => absurd h (by omega))

theorem cent : (allN 1100 (fun i => ltF (fl (CR.TF i))) && eqF (fl (CR.TF 0)) r0F) = true := by
  quickRfl

end CFSG.KD.HS589207.Rec

end
