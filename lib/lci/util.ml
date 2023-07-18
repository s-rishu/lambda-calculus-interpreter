(** {0} Utility functions *)

(** Source code position, line:column *)
type pos = { pos_line: int; pos_col: int }

(** A dummy source code position *)
let dummy_pos = { pos_line = 0; pos_col = 0 }

(** Create an error message for a given source code position [pos] and string [msg]. 
  * Then throw it as a [Failure] exception. *)
let fail pos msg = failwith (Printf.sprintf "Error:%d:%d: %s" pos.pos_line pos.pos_col msg)
