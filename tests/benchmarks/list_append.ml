let preds = [| "mem"; "hd"; "ord" |]

let post (f : CustomStk.t) (r : CustomStk.t) (f' : CustomStk.t) (r' : CustomStk.t)
    (u : int) (v : int) =
  iff (mem f' u || mem r' u || hd f u) (mem f u || mem r u)
  && implies (ord f' u v || ord r' v u) (ord f u v || ord r v u)