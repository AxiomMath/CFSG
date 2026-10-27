module

public import Certificates.Data.Kernel.KDense.Twins
public import Certificates.Data.Kernel.SortTree
public import CFSG.Monster.B.Rep4371.Model
public import Certificates.Data.CFSGNative.MonsterB.CosetEnum
import CFSG.Certificates.Kernel.Common.HexTree

public section

namespace CertificateChecks.Coset3023

open CFSG.KC.KDense CFSG.KLie.CT CFSG.Monster.B

@[expose] noncomputable def tb (x : Nat) : Bool := Nat.beq x (nat_lit 1)

@[expose] def THText : String := include_str "Coset3023/theta.hex"

@[expose] noncomputable def TH : Nat → Nat := by hex_tree THText 16384 8574797257524458424 256

@[expose] noncomputable def thetaL (x : Nat) : Nat :=
  Nat.land (CFSG.KC.SortTree.recT TH 6 16 (Nat.land x (nat_lit 4095))) (nat_lit 4095)

@[expose] noncomputable def mulW (x y : Model.Pauli) : Model.Pauli :=
  (x.1 ^^ y.1 ^^ tb (pairT y.2.1 x.2.2), Nat.xor x.2.1 y.2.1, Nat.xor x.2.2 y.2.2)

@[expose] noncomputable def conjTW (e b : Nat) : Model.Pauli :=
  (tb (pairT e (thetaL b)), Nat.xor b (selB (pairT b (thetaL e)) (nat_lit 63)),
    dualT (Nat.land (wordT e) (wordT b)))

@[expose] noncomputable def conjDW (e : Nat) (pe : Bool) (d : Nat) : Model.Pauli :=
  (fun o q => (tb (Nat.land (Nat.xor o (nat_lit 1)) q),
    Nat.xor (selB o e) (selB (Nat.xor (Nat.land o pe.toNat) q) (nat_lit 63)),
    Nat.xor (selB o (thetaL e)) d)) (pairT (nat_lit 63) d) (pairT e d)

@[expose] noncomputable def conjYW (e : Nat) (pe : Bool) (y : Model.Pauli) : Model.Pauli :=
  mulW (mulW (y.1, nat_lit 0, nat_lit 0) (conjTW e y.2.1)) (conjDW e pe y.2.2)

@[expose] noncomputable def conjPermW (P BT : Nat) (y : Model.Pauli) : Model.Pauli :=
  (y.1 ^^ tb (kappaT BT y.2.1), permCT P y.2.1,
    Nat.xor (thetaL (permCT P y.2.1)) (permDT P (Nat.xor (thetaL y.2.1) y.2.2)))

@[expose] noncomputable def alphaW (e : Nat) (pe : Bool) (P BT : Nat) (y : Model.Pauli) : Model.Pauli :=
  conjPermW P BT (conjYW e pe y)

@[expose] noncomputable def decW (r : Nat) : Model.Pauli :=
  (tb (Nat.land (Nat.shiftRight r (nat_lit 24)) (nat_lit 1)), Nat.land r (nat_lit 4095),
    Nat.land (Nat.shiftRight r (nat_lit 12)) (nat_lit 4095))

@[expose] noncomputable def PP (c : Nat) : Nat :=
  nIf(Nat.beq c 1, 984818244535754528103549039458486304, nIf(Nat.beq c 2, 984818244535754528103549039458486304, 899228929685057613473567618418055332))

@[expose] def imgs1L : Array Model.Pauli :=
  #[(false, 1, 60), (false, 2, 60), (false, 59, 3), (false, 55, 3), (false, 47, 3), (false, 31,
    3), (true, 64, 128), (true, 128, 64), (true, 256, 512), (true, 512, 256), (false, 1024, 0),
    (false, 2048, 0), (false, 60, 61), (false, 60, 62), (false, 3, 56), (false, 3, 52), (false,
    3, 44), (false, 3, 28), (false, 0, 64), (false, 0, 128), (false, 0, 256), (false, 0, 512),
    (false, 0, 1024), (false, 0, 2048)]

@[expose] def imgs2L : Array Model.Pauli :=
  #[(false, 62, 222), (false, 2, 289), (false, 59, 33), (false, 8, 2721), (false, 16, 2913),
    (false, 32, 30), (false, 127, 2833), (false, 191, 2569), (true, 256, 2642), (true, 512,
    472), (true, 1024, 2048), (true, 2111, 1496), (false, 737, 2244), (false, 734, 2247),
    (false, 734, 2241), (false, 734, 2253), (false, 734, 2261), (false, 737, 2277), (true, 63,
    64), (true, 63, 128), (false, 0, 256), (true, 63, 512), (false, 0, 1024), (false, 0, 2048)]

@[expose] noncomputable def SB (c : Nat) : Nat :=
  nIf(Nat.beq c 1, 1122434596908642094079483101069855082346922415210496,
    386015624722304984601096676673172203823670424856815264134487908557656348468821099230)

@[expose] noncomputable def SC (c : Nat) : Nat :=
  nIf(Nat.beq c 1, 3317530067214616151107973136333259959070897499484853276961148929,
    1852673538251969904426707272359754440539910929764644965769165488704244756277745)

@[expose] def T1Text : String := include_str "Coset3023/tab1.hex"
@[expose] def T2Text : String := include_str "Coset3023/tab2.hex"
@[expose] def T6Text : String := include_str "Coset3023/tab6.hex"
@[expose] def J1Text : String := include_str "Coset3023/join1.hex"
@[expose] def J2Text : String := include_str "Coset3023/join2.hex"
@[expose] def J6Text : String := include_str "Coset3023/join6.hex"
@[expose] def C1Text : String := include_str "Coset3023/cls1.hex"
@[expose] def C2Text : String := include_str "Coset3023/cls2.hex"
@[expose] def EDText : String := include_str "Coset3023/edges.hex"

@[expose] noncomputable def T1 : Nat → Nat := by hex_tree T1Text 51200 469240985946983924 400
@[expose] noncomputable def T2 : Nat → Nat := by hex_tree T2Text 51200 12703176340809776093 400
@[expose] noncomputable def T6 : Nat → Nat := by hex_tree T6Text 51200 3563859102286211758 400
@[expose] noncomputable def J1 : Nat → Nat := by hex_tree J1Text 51200 8042266263720635936 800
@[expose] noncomputable def J2 : Nat → Nat := by hex_tree J2Text 51200 11677853824867742324 800
@[expose] noncomputable def J6 : Nat → Nat := by hex_tree J6Text 51200 10082429107528199421 800
@[expose] noncomputable def CL1 : Nat → Nat := by hex_tree C1Text 771584 2227838244757116523 704
@[expose] noncomputable def CL2 : Nat → Nat := by hex_tree C2Text 96256 8276425971594925963 752
@[expose] noncomputable def ED : Nat → Nat := by hex_tree EDText 24576 8302580226625194140 128

end CertificateChecks.Coset3023

end
