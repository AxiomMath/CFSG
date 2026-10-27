module

public import CFSG.Quasithin.H13.L32N1449Inputs
public import Certificates.Data.Kernel.Mat8P
public import Certificates.Kernel.H13.Data
public import Certificates.Kernel.H13.DataQ1449
public import Certificates.Kernel.H13.DataQ1449Inv
import CFSG.Certificates.Kernel.Mat8PSound

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.O3Cert CFSG.Quasithin.H13.Q1449Cert
  CFSG.KC.Mat8P

@[expose] noncomputable def noCommP (O : List ℕ) (X : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun A _ ih => !(Nat.beq (mulP A X) (mulP X A)) && ih) O

@[expose] noncomputable def invsP (G : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) []
    (fun X _ ih => bif !(Nat.beq X oneP) && Nat.beq (mulP X X) oneP then X :: ih else ih) G

@[expose] noncomputable def invOK (O : List ℕ) (X : ℕ) : Bool :=
  noCommP O X || small64B (unpackM X) || fullAltB (unpackM X)

@[expose] noncomputable def qtab (w : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight
    (nat_lit 40868313831888203015624906566168296547668046309358535763386510883391707021312) w)
    (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def qbit (v : ℕ) : Bool := qtab (Nat.land v (nat_lit 255))

set_option maxRecDepth 100000

theorem quadN_lt_eq : ((List.range 256).all fun w =>
    CFSG.Quasithin.H13.G5Cert.quadN w == qtab w) = true := by
  simp only [CFSG.Quasithin.H13.G5Cert.quadN, mv8_toR]
  decide +kernel

theorem quadN_and (v : ℕ) :
    CFSG.Quasithin.H13.G5Cert.quadN v = CFSG.Quasithin.H13.G5Cert.quadN (v &&& 255) := by
  have t : ∀ i, i < 8 → (255 : ℕ).testBit i = true := by decide
  simp only [CFSG.Quasithin.H13.G5Cert.quadN, CFSG.Quasithin.H13.S8Cert.dotN, mv8, bt,
    Nat.testBit_and, t 0 (by decide), t 1 (by decide), t 2 (by decide), t 3 (by decide),
    t 4 (by decide), t 5 (by decide), t 6 (by decide), t 7 (by decide), Bool.and_true]

theorem quadN_eq (v : ℕ) : CFSG.Quasithin.H13.G5Cert.quadN v = qbit v := by
  have h := List.all_eq_true.mp quadN_lt_eq (v &&& 255)
    (List.mem_range.mpr (Nat.and_lt_two_pow (n := 8) v (by decide)))
  rw [quadN_and, eq_of_beq h]
  rfl

theorem invsL0_beq : (invsP D.h2L == D.invL0) = true := by decide +kernel

theorem invsL1_beq : (invsP D.omNL == D.invL1) = true := by decide +kernel

macro "inv_ok_tac" : tactic => `(tactic| (
  simp only [invOK, small64B, fullAltB, smallImgB, fullImgB, imgBasis,
    CFSG.Quasithin.H13.G5Cert.b5N, quadN_eq, decide_isChain_toP, mv8_toR]
  decide +kernel))

set_option maxHeartbeats 0 in
theorem invOK0a : ((D.invL0.take 160).all fun X => invOK D.o5L0 X) = true := by inv_ok_tac

set_option maxHeartbeats 0 in
theorem invOK0b : ((D.invL0.drop 160).all fun X => invOK D.o5L0 X) = true := by inv_ok_tac

set_option maxHeartbeats 0 in
theorem invOK1a : ((D.invL1.take 240).all fun X => invOK D.o5L1 X) = true := by inv_ok_tac

set_option maxHeartbeats 0 in
theorem invOK1b : ((D.invL1.drop 240).all fun X => invOK D.o5L1 X) = true := by inv_ok_tac

end CertificateChecks.KernelH13

end
