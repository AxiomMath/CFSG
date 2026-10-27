module

public import Certificates.Kernel.TcRes.Checks
public import CFSG.Certificates.Kernel.TcRes.PlaneSound
public import CFSG.Certificates.Kernel.TcRes.TransSound
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Index

public section

namespace CFSG.KD.TcRes.ch715750glue

open CFSG.KD.TcRes CFSG.KC.TcRes CFSG.TcRes.TK CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

theorem e6_sym : ∀ i j : Fin Tag.E6.rank, Tag.E6.symmetrizedCartan i j = Tag.E6.cartan i j :=
  fun i j => by simp [Tag.symmetrizedCartan, Tag.symmetrizer]

theorem e8_sym : ∀ i j : Fin Tag.E8.rank, Tag.E8.symmetrizedCartan i j = Tag.E8.cartan i j :=
  fun i j => by simp [Tag.symmetrizedCartan, Tag.symmetrizer]

theorem e6_yc' : ∀ m (hm : m < 6) k (hk : k < 6), (fld (E6.yc m) 16 (6 - 1 - k) : ℤ) -
    fld (E6.yc m) 16 (2 * 6 - 1 - k) = Tag.cartanE 6 ⟨m, hm⟩ ⟨k, hk⟩ := by
  decide +kernel

theorem e8_yc' : ∀ m (hm : m < 8) k (hk : k < 8), (fld (E8.yc m) 16 (8 - 1 - k) : ℤ) -
    fld (E8.yc m) 16 (2 * 8 - 1 - k) = Tag.cartanE 8 ⟨m, hm⟩ ⟨k, hk⟩ := by
  decide +kernel

theorem e6_yc : ∀ m k : Fin Tag.E6.rank, (fld (E6.yc m) 16 (Tag.E6.rank - 1 - k) : ℤ) -
    fld (E6.yc m) 16 (2 * Tag.E6.rank - 1 - k) = Tag.E6.symmetrizedCartan m k := by
  intro m k
  rw [e6_sym]
  exact e6_yc' m.1 m.2 k.1 k.2

theorem e8_yc : ∀ m k : Fin Tag.E8.rank, (fld (E8.yc m) 16 (Tag.E8.rank - 1 - k) : ℤ) -
    fld (E8.yc m) 16 (2 * Tag.E8.rank - 1 - k) = Tag.E8.symmetrizedCartan m k := by
  intro m k
  rw [e8_sym]
  exact e8_yc' m.1 m.2 k.1 k.2

theorem e6_ycb' : ∀ m < 6, E6.yc m < 2 ^ (32 * 6) := by
  decide +kernel

theorem e8_ycb' : ∀ m < 8, E8.yc m < 2 ^ (32 * 8) := by
  decide +kernel

theorem e6_ycb : ∀ m : Fin Tag.E6.rank, E6.yc m < 2 ^ (32 * Tag.E6.rank) :=
  fun m => e6_ycb' m.1 m.2

theorem e8_ycb : ∀ m : Fin Tag.E8.rank, E8.yc m < 2 ^ (32 * Tag.E8.rank) :=
  fun m => e8_ycb' m.1 m.2

theorem e6D : DatumRaw Tag.E6 72 (vecOf Tag.E6.rank E6.V) (fun g v => fld (E6.rt g) 7 v)
    (fun g v => Nat.beq (fld (fld E6.ADJ 72 g) 1 v) 1) (fun i => fld E6.NEG 7 i) :=
  datumRaw_of_checks Tag.E6 (W := 7) (yc := E6.yc) (rtR := E6.rt) (V := E6.V) (X := E6.X)
    (Y := E6.Y) (NEG := E6.NEG) (PAR := E6.PAR) (SRT := E6.SRT) (ADJ := E6.ADJ) e6_sym e6_yc
    e6_ycb (by decide) ch715750all.e6_root ch715750all.e6_row ch715750e6.srt

theorem e8D : DatumRaw Tag.E8 240 (vecOf Tag.E8.rank E8.V) (fun g v => fld (E8.RTs g) 8 v)
    (fun g v => Nat.beq (fld (fld E8.ADJ 240 g) 1 v) 1) (fun i => fld E8.NEG 8 i) :=
  datumRaw_of_checks Tag.E8 (W := 8) (yc := E8.yc) (rtR := E8.RTs) (V := E8.V) (X := E8.X)
    (Y := E8.Y) (NEG := E8.NEG) (PAR := E8.PAR) (SRT := E8.SRT) (ADJ := E8.ADJ) e8_sym e8_yc
    e8_ycb (by decide) ch715750all.e8_root ch715750all.e8_row ch715750e8.srt

theorem e6F : ForestRaw (vecOf Tag.E6.rank E6.V) 72 51840 25 (fun p => keyOf (ent C1.LF p))
    (fun k => Nat.land (Nat.shiftRight C1.REPS (k * 42)) M42) :=
  forestRaw_of_checks (RT := E6.RT) (LF := C1.LF) (REPS := C1.REPS) (WRD := C1.WRD) e6D
    ch715750all.c1_leaf ch715750all.c1_rep

theorem e6_conj_rep
    (g : WeylGroup Tag.E6) : ∃ k < 25, ∃ w', TupleOf (vecOf Tag.E6.rank E6.V) 72
      (Nat.land (Nat.shiftRight C1.REPS (k * 42)) M42) w' ∧ IsConj w' g :=
  forall_isConj_rep e6D e6F CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_weylGroup_E6 g

theorem c1_sweep {q : ℕ}
    (hq : q < 75) (h70 : q ≠ 70) (h71 : q ≠ 71) {w : WeylGroup Tag.E6}
    (hw : TupleOf (vecOf Tag.E6.rank E6.V) 72
      (Nat.land (Nat.shiftRight C1.REPS (q / 3 * 42)) M42) w) :
    SweepRaw (KSet w (sOf (q % 3) : ZMod 3)) (fld C1P.START 16 q) (fld C1P.START 16 (q + 1))
      (fun p => (v3 (pu1 (prec C1P.LF p)), v3 (pu2 (prec C1P.LF p)))) :=
  sweepRaw_of_checks (U := C1P.uS) (RC := C1P.rcS) (L := C1P.lS) (M := C1P.mS) rfl e6D
    ch715750all.p_tab ch715750all.p_rc hq (ch715750all.p_sw q hq h70 h71) hw

theorem e8_beta0 :
    ∀ g < 240, iform (vecOf Tag.E8.rank E8.V g) (vecOf Tag.E8.rank E8.V 0) = 0 →
      ∃ h : WeylGroup Tag.E8, h • vecOf Tag.E8.rank E8.V 0 = vecOf Tag.E8.rank E8.V 0 ∧
        h • vecOf Tag.E8.rank E8.V (fld E8T.T0 8 0) = vecOf Tag.E8.rank E8.V g :=
  btRaw_of_checks (BT := E8T.BT) e8D ch715751t.bt

theorem t0_lt : ∀ j < 8, fld E8T.T0 8 j < 240 := by decide +kernel

theorem c2_ker0 : KerRaw (vecOf Tag.E8.rank E8.V) E8T.T0 C2P.B0 C2P.PV0 C2P.MW0 2 :=
  kerRaw_of_checks (RC := C2P.rcS) rfl (by norm_num) t0_lt ch715750all.c2p_rc ch715751p.k0

theorem c2_ker1 : KerRaw (vecOf Tag.E8.rank E8.V) E8T.T0 C2P.B1 C2P.PV1 C2P.MW1 3 :=
  kerRaw_of_checks (RC := C2P.rcS) rfl (by norm_num) t0_lt ch715750all.c2p_rc ch715751p.k1

end CFSG.KD.TcRes.ch715750glue

end
