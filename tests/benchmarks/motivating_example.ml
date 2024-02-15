let preds = [| "sorted"; "hd"; "mem" |]

let pre (l : Customstk.t) (i : int) (v : bool) =
  (sorted l)

let post (l : Customstk.t) (i : int) (v : bool) (u:int) =
  implies (mem u l) (implies (u <= i) v)
