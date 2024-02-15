let preds = [| "mem"; "hd" |]

let post (f : Batchedq.t) (r : Batchedq.t) (f' : Batchedq.t) (r' : Batchedq.t)
    (u : int) =
  iff (mem f' u || hd f u || mem r' u) (mem f u || mem r u)
