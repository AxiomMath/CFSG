module

public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import CFSG.Sporadic.Recognition.HeMultiplierInputs
public meta import CFSG.Sporadic.Recognition.HeMultiplierInputs
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.KD.HeMult

open CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Recognition.HeMultiplier

meta def orbM : VOrbit := orbitData ()

meta def natsM (t : Table) : Array Nat := t.map (·.toNat)

meta def ctM : Array Nat := natsM (wordT 8330 (genTables orbM) cW)
meta def wuM : Array Nat := natsM (wordT 8330 (genTables orbM) (acW uAC))
meta def wvM : Array Nat := natsM (wordT 8330 (genTables orbM) (acW vAC))
meta def wsM : Array Nat := natsM (wordT 8330 (genTables orbM) (acW sAC))
meta def uM : Array Nat := natsM (heImg orbM 0)
meta def vM : Array Nat := natsM (heImg orbM 1)
meta def sM : Array Nat := natsM (heImg orbM 2)
meta def tM : Array Nat := natsM (heImg orbM 3)
meta def uiM : Array Nat := natsM (invT 8330 (heImg orbM 0))
meta def viM : Array Nat := natsM (invT 8330 (heImg orbM 1))
meta def siM : Array Nat := natsM (invT 8330 (heImg orbM 2))
meta def tiM : Array Nat := natsM (invT 8330 (heImg orbM 3))

end CFSG.KD.HeMult

#krows CFSG.KD.HeMult.CT CFSG.KD.HeMult.ctM
#krows CFSG.KD.HeMult.Wu CFSG.KD.HeMult.wuM
#krows CFSG.KD.HeMult.Wv CFSG.KD.HeMult.wvM
#krows CFSG.KD.HeMult.Ws CFSG.KD.HeMult.wsM
#krows CFSG.KD.HeMult.U CFSG.KD.HeMult.uM
#krows CFSG.KD.HeMult.V CFSG.KD.HeMult.vM
#krows CFSG.KD.HeMult.S CFSG.KD.HeMult.sM
#krows CFSG.KD.HeMult.T CFSG.KD.HeMult.tM
#krows CFSG.KD.HeMult.Ui CFSG.KD.HeMult.uiM
#krows CFSG.KD.HeMult.Vi CFSG.KD.HeMult.viM
#krows CFSG.KD.HeMult.Si CFSG.KD.HeMult.siM
#krows CFSG.KD.HeMult.Ti CFSG.KD.HeMult.tiM

end
