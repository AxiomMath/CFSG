module

public meta import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.LocalComp.BfsGen

public section

namespace CFSG.KC.ListBridgeGen

meta def treeRecs (n w : Nat) (gens : Array (Array Nat)) : List Nat := Id.run do
  let (pts, edges) := CFSG.KC.BfsGen.search n w gens
  let mut par : Array Nat := Array.replicate pts.size 0
  let mut gen : Array Nat := Array.replicate pts.size 0
  let mut dep : Array Nat := Array.replicate pts.size 0
  let mut seen : Array Bool := (Array.replicate pts.size false).set! 0 true
  for i in [0:edges.size] do
    let row := edges[i]!
    for k in [0:row.size] do
      let j := row[k]!
      if !seen[j]! then
        seen := seen.set! j true
        par := par.set! j i
        gen := gen.set! j k
        dep := dep.set! j (dep[i]! + 1)
  return (List.range pts.size).map fun j => par[j]! + 65536 * (gen[j]! + 256 * dep[j]!)

end CFSG.KC.ListBridgeGen

end
