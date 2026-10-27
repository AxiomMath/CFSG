module

public section

namespace CertificateChecks.KernelSporSch.QueueGen

meta def queue (n : Nat) (gens : Array (Array Nat)) (roots : Array Nat) : Array Nat := Id.run do
  let mut seen : Array Bool := Array.replicate n false
  let mut queue : Array Nat := #[]
  for r in roots do
    if r < n && !seen[r]! then
      seen := seen.set! r true
      queue := queue.push r
  let mut head := 0
  for _ in [0:n] do
    if head < queue.size then
      let x := queue[head]!
      head := head + 1
      for k in [0:gens.size] do
        let y := (gens[k]!)[x]!
        if y < n && !seen[y]! then
          seen := seen.set! y true
          queue := queue.push y
  return queue

meta def ord (n : Nat) (q : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate n 0
  for t in [0:q.size] do
    r := r.set! q[t]! t
  return r

meta def events (kG R : Nat) (q o par gl : Array Nat) : Array Nat :=
  (Array.range q.size).map fun t => if t < R then 0 else kG * o[par[q[t]!]!]! + gl[q[t]!]!

end CertificateChecks.KernelSporSch.QueueGen

end
