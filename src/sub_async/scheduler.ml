(** Task scheduler for async evaluation with non-deterministic execution order. *)

type task = unit -> unit

let queue : task Queue.t = Queue.create ()
let verbose = ref true

(** Schedule a task for later execution *)
let schedule task =
  Queue.add task queue

(** Run all scheduled tasks until queue is empty *)
let run_all () =
  while not (Queue.is_empty queue) do
    let task = Queue.take queue in
    task ()
  done

(** Pick a random task from queue and execute it *)
let run_one_random () =
  if not (Queue.is_empty queue) then begin
    let len = Queue.length queue in
    let idx = Random.int len in
    (* Convert to list, pick one, put rest back *)
    let tasks = Queue.fold (fun acc t -> t::acc) [] queue in
    Queue.clear queue;
    let rec rebuild i = function
      | [] -> ()
      | t::rest ->
          if i = idx then begin
            if !verbose then
              Printf.printf "[scheduler] Executing randomly selected task\n%!";
            t ()  (* Execute selected task *)
          end else
            Queue.add t queue;
          rebuild (i+1) rest
    in
    rebuild 0 (List.rev tasks)
  end

(** Check if queue is empty *)
let is_empty () = Queue.is_empty queue

(** Reset scheduler state *)
let reset () =
  Queue.clear queue
