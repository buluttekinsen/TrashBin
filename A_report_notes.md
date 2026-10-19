# Person A – draft report material (control process + §5.4 Multiple users / Bin sensor)

> Draft. Rewrite in your own words, and **read the code until you can explain every label**.
> Under §1.1 you are responsible for everything you submit. Declare in the AI section that
> the control process, the truck process and the draft properties were written with AI
> assistance, and say what you kept or changed.
> All timings below were measured in a sandbox with TLC 2.19 (= Toolbox 1.7.4). Re-measure on your laptop.

---

## 1. Control process (single bin)

**Structure.** One infinite loop (`ControlLoop`). Each iteration handles exactly one event, chosen with `either/or`.
The events have a fixed priority, enforced through the guards:

1. **Truck arrived** → send `start_emptying` (only when `binCommand = "finished"`).
2. **Bin full and truck idle** → send `request`.
3. **Scan available** (only when 1 and 2 are not enabled) → handle the scan.

*Why priorities.* `fair process` only guarantees that the control process steps eventually, not that every branch is
taken. Without priorities the control could answer an endless stream of scans and never serve the truck, and
`TrashEmptied` / `TruckEmpties` would fail even under weak fairness.

**Handling a scan.**
`read(scans)` → write server request → read server response → if `permission ∧ truck idle ∧ TrashFitsCapacity(MaxUserTrash)`:

| Step | Action | Why |
|---|---|---|
| `ControlUnlock` | unlock outer door | `change_outer_door` needs an unlocked door; unlocking only on grant means unauthorised users never get an unlocked door |
| `ControlGrant` | write `granted = TRUE` | only after the unlock has finished |
| `ControlAwaitClosed` | wait for `binSensor = outer_door_closed` and `finished`, then lock | door must be locked before the trap door moves |
| `ControlOpenTrap` | open trap door | trash falls into the compartment |
| `ControlExtendRam` | extend ram | trap door is open, so no destruction; compresses |
| `ControlRetractRam` | retract ram | ram must be retracted before the trap door changes again |
| `ControlCloseTrap` | close trap door | `empty` requires a closed trap door |

otherwise write `granted = FALSE` immediately (invalid card, truck on the way, or no room).

**Modelling decisions.**
- *Capacity check:* grant only if `Trash + MaxUserTrash <= trashCapacity` (Note 10). The control cannot know how much the user carries.
- *Every bin command is preceded by `await binCommand.command = "finished"`.* Otherwise the bin's later
  `binCommand.command := "finished"` (label `BinCommandFinished`) would overwrite a newer command. Because all
  awaits are in the same step as the send, there is no race.
- *When to request a truck:* when the bin cannot take another maximal deposit (`BinFull`), i.e. exactly when the control
  would have to decline every scan anyway. Not after every deposit.
- *While the truck is reserved:* scans are still read and answered (declined). The control never blocks on the truck.
- *Door stays locked by default,* unlocked only between grant and the user closing it.
- *Few labels:* the lock command is merged into `ControlAwaitClosed`; the decline branch needs no label. Fewer labels = fewer states.

**Truck handshake** (agreed with person B): `emptied` (idle) → `request` → `arrived` → `start_emptying` → `emptied`.
The control only answers `arrived` when it is between two deposits, so the bin is guaranteed safe (door locked, trap closed,
ram retracted, nothing in the outer door). The truck then sends `empty` itself.

## 2. Control process (multiple bins)

Adaptations compared to single:
- bin/user/truck indexed by `scan.bin`, `scan.user`, `truckCommand[t]`;
- bin and truck status are **derived** from `truckCommand` (`BinReserved(b)`, `AvailableTrucks`, `NeedyBins`, `ReadyTrucks`), so the control keeps no extra state;
- **truck strategy:** a truck is requested for a bin when `BinFull(b)` and no truck is reserved for it. Bin and truck are picked deterministically (lowest id) with `CHOOSE`. This keeps the state space small;
- same priority order (arrived truck > request > scan);
- deposits are handled one at a time, the scan queue is FIFO. Trucks (several can travel simultaneously) and scans are interleaved, so scans are answered while a truck is on its way;
- a declined/granted decision for bin `b` only looks at bin `b`, so bins do not block each other.

**Why sequential deposits:** they keep the model verifiable within the 5-minute limit (see table) and make the safety argument simple (the bin is always idle when `arrived` is handled).

## 3. Verification results (draft numbers, sandbox)

| Model | Config | Deadlock | Invariants | Properties | Distinct states | Time |
|---|---|---|---|---|---|---|
| single | 1/1/1, cap 7, max 4 | none | all hold | all hold (WF) | 7,052 | 4 s |
| multiple | Bins 2/1/1, cap 3, max 2 | none | all hold | all hold (WF) | 75,424 | 37 s |
| multiple | Users 1/2/1, cap 3, max 2 | none | all hold | `UserTrash`, `UserTrashDeposited` **fail**; others hold | 104,384 | 47 s |
| multiple | Trucks 2/1/2, cap 2, max 1 | none | all hold | all hold (WF) | 118,102 | 80 s |

Fairness: all processes are `fair process` (weak fairness). Without fairness all four liveness properties fail with a stuttering counter-example (checked for single).
`AuthorizedOpenOnly` is still `FALSE` (person B's job) and is not part of these runs.

## 4. §5.4 Multiple users

Both `UserTrash` and `UserTrashDeposited` are violated for **Users** (bin 1, users 2 and 3, truck 4).

**Counter-example (lasso found by TLC, loop starts at state 88 of 176).** User 3 deposits twice per cycle and the second deposit makes
`BinFull` true. The control then requests the truck, and user 2's scan is handled while the bin is reserved, so it is declined. User 2
rescans. After the truck has emptied the bin the queue head is user 3 again, which deposits, and the cycle repeats. User 2 holds
trash forever (`userTrash[2] > 0` always), so `<>(userTrash[2] = 0)` fails, and `[]<>(userTrash[2] = 0)` fails too.

**Fairness.** Violation remains under weak fairness (that is the model's `Spec`) and under strong fairness of all processes (checked with an
SF variant of `Spec`). Fairness only says every process steps eventually, not in which order scans are queued relative to the
truck cycle. User 2's scan step is enabled continuously, so strong fairness adds nothing.

**More trucks/bins.** Adding a second truck (1 bin, 2 users, 2 trucks) still violates `UserTrashDeposited` (checked). The problem is the arbitration
between users, not the lack of emptying capacity. A second bin: the run with 2 bins, 2 users, 1 truck did not finish
within 280 s (>800k distinct states, no violation found yet), so no claim. Argue it from the trace instead, or run it longer.

**Why the control does not prevent it:** declined scans get no memory. A declined user must rescan and goes to the back of the queue,
so nothing guarantees it is served first after the truck has emptied the bin. A fix would be a reservation or a priority for users that have been declined.

## 5. §5.4 Bin sensor

Experiment (temporary change, single model): replace
`await binSensor.sensor = "outer_door_closed" /\ binCommand.command = "finished"` in `ControlAwaitClosed` by only `await binCommand.command = "finished"`.

Result: TLC reports `Failure of assertion at line 171` (`assert ~outerDoorLocked` for `change_outer_door`). Trace: after `ControlGrant` the
`binCommand` is already `finished` (from the unlock), so the control continues at once, locks the door again (states 13–15) and only then does the user send
`change_outer_door`; the bin finds the door locked. The command `finished` says only that the **last command** has been executed, not that the user closed the door.
The user opens/closes the door without the control knowing, so the sensor is the only signal for "deposit done".
The required behaviour (move the trash only after the user has closed the door) is not preserved.
Why the sensor is also awaited together with `finished`: the bin sets the sensor in one step and `finished` in the next, so the control could otherwise overwrite the unfinished user command.
