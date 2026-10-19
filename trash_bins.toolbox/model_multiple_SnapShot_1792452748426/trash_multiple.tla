--------------------------- MODULE trash_multiple ---------------------------

EXTENDS trash_data

(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bins
  outerDoorOpen = [b \in Bins |-> FALSE],
  outerDoorLocked = [b \in Bins |-> TRUE],
  trapDoorOpen = [b \in Bins |-> FALSE],
  ramExtended = [b \in Bins |-> FALSE],
  trashInTop = [b \in Bins |-> 0],
  trashCompressed = [b \in Bins |-> 0],
  trashUncompressed = [b \in Bins |-> 0],
  trashCapacity = [b \in Bins |-> MaxCapacity],
  trapDestroyed = [b \in Bins |-> FALSE],

  \* Variables for users
  userTrash = [u \in Users |-> 0],

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]],
  \* Sensor from outer door of bin
  binSensor = [b \in Bins |-> [sensor |-> "idle"]],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = [u \in Users |-> << >>],
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Commands for the trucks
  truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]],
  \* Ghost variable (Note 12): last verdict of the server for each user
  verdict = [u \in Users |-> FALSE];

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]
AvailableTrucks == {t \in Trucks : truckCommand[t].command = "emptied"}

BinFull(bin) == ~TrashFitsCapacity(bin, MaxUserTrash)
BinReserved(bin) == \E t \in Trucks : /\ truckCommand[t].bin = bin
                                      /\ truckCommand[t].command \in {"request", "arrived", "start_emptying"}
NeedyBins == {b \in Bins : BinFull(b) /\ ~BinReserved(b)}
ArrivedTrucks == {t \in Trucks : truckCommand[t].command = "arrived"}
ReadyTrucks == {t \in ArrivedTrucks : binCommand[truckCommand[t].bin].command = "finished"}
PickBin == CHOOSE b \in NeedyBins : TRUE
PickTruck == CHOOSE t \in AvailableTrucks : TRUE
PickReady == CHOOSE t \in ReadyTrucks : TRUE

\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins
          /\ \A u \in Users : verdict[u] \in BOOLEAN

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1

\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)

\*****************************
\* Properties of interest
\*****************************
\* For each trash bin, the outer door can only be locked if it is closed.
OuterDoorLocked == \A b \in Bins : outerDoorLocked[b] => ~outerDoorOpen[b]
\* For each trash bin, the vertical ram is only used when the outer door is closed and locked.
RamOuterDoor == \A b \in Bins : ramExtended[b] => (~outerDoorOpen[b] /\ outerDoorLocked[b])
\* For each trash bin, every time it is full, it is eventually not full anymore.
TrashEmptied == \A b \in Bins : [](BinFull(b) => <>(~BinFull(b)))
\* Each user infinitely often has trash and infinitely often has no trash.
UserTrash == \A u \in Users : ([]<>(userTrash[u] > 0) /\ []<>(userTrash[u] = 0))
\* For each user, every time they have trash they can deposit their trash.
UserTrashDeposited == \A u \in Users : [](userTrash[u] > 0 => <>(userTrash[u] = 0))
\* For each trash bin, every time a truck is requested for it, a truck has eventually emptied it.
TruckEmpties == \A b \in Bins :
  [](  (\E t \in Trucks : truckCommand[t].command = "request" /\ truckCommand[t].bin = b)
       => <>(trashCompressed[b] = 0)  )

end define;

\*****************************
\* Helper macros
\*****************************

\* Compress trash
macro compress(compressed, uncompressed) begin
  compressed := compressed + IF (uncompressed > 1) THEN uncompressed \div 2 ELSE uncompressed;
  uncompressed := 0;
end macro

\* Read res from queue.
\* The macro awaits a non-empty queue.
macro read(queue, res) begin
  await queue /= <<>>;
  res := Head(queue);
  queue := Tail(queue);
end macro

\* Write msg to the queue.
macro write(queue, msg) begin
  queue := Append(queue, msg);
end macro

\*****************************
\* Process for a bin
\*****************************
fair process binProcess \in Bins
begin
  BinWaitForCommand:
    while TRUE do
      await binCommand[self].command /= "finished";
      if binCommand[self].command = "change_outer_door" then
        \* Open/Close outer door
        assert ~outerDoorLocked[self];
        outerDoorOpen[self] := binCommand[self].open;
        if ~outerDoorOpen[self] then
          binSensor[self] := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand[self].command = "change_outer_lock" then
        \* Lock/Unlock outer door
        assert ~outerDoorOpen[self];
        outerDoorLocked[self] := ~(binCommand[self].open);
      elsif binCommand[self].command = "change_trap_door" then
        assert outerDoorLocked[self];
        \* Open/Close trap door
        if ramExtended[self] \/ CapacityExceeded(self) then
            trapDestroyed[self] := TRUE;
        end if;
        trapDoorOpen[self] := binCommand[self].open;
        if trapDoorOpen[self] then
          \* Trash falls through
          trashUncompressed[self] := trashUncompressed[self] + trashInTop[self];
          trashInTop[self] := 0;
        end if
      elsif binCommand[self].command = "change_ram" then
        assert outerDoorLocked[self];
        \* Extend/Retract ram
        ramExtended[self] := binCommand[self].open;
        if ramExtended[self] then
          if ~trapDoorOpen[self] then
            trapDestroyed[self] := TRUE;
          end if;
          \* Compress trash
          compress(trashCompressed[self], trashUncompressed[self]);
        end if;
      elsif binCommand[self].command = "empty" then
        \* Empty trash bin
        assert outerDoorLocked[self];
        assert ~trapDoorOpen[self];
        assert ~ramExtended[self];
        assert trashInTop[self] = 0;
        assert trashUncompressed[self] = 0;
        trashCompressed[self] := 0;
      else
        \* should not happen
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand[self].command := "finished";
    end while;
end process;

\*****************************
\* Process for a user
\*****************************
fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE],
  selectedBin = 0
begin
  UserNextIteration:
    while TRUE do
      if userTrash[self] = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash[self] := amt;
        end with;
      end if;
  UserScanCard:
      \* Non-deterministically choose a bin
      with sBin \in Bins do
        selectedBin := sBin;
        write(scans, [user |-> self, bin |-> selectedBin]);
      end with;
  UserAwaitScanResponse:
      read(permissions[self], perm);
      assert perm.user = self;
      assert perm.bin = selectedBin;
      if perm.granted then
  UserOpenDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand[selectedBin].command = "finished";
  UserDepositTrash:
        assert trashInTop[selectedBin] = 0;
        trashInTop[selectedBin] := userTrash[self];
        userTrash[self] := 0;
  UserCloseDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand[selectedBin].command = "finished";
      end if;
    end while;
end process;

\*****************************
\* Process for a server
\*****************************
fair process serverProcess = Server
variables
  req = [user |-> 0]
begin
  ServerNextIteration:
    while TRUE do
  ServerAwaitRequest:
      read(serverRequests, req);
      with valid \in ValidCard(req.user) do
        write(serverResponses, [user |-> req.user, permission |-> valid]);
        verdict[req.user] := valid;
      end with;
    end while;
end process;

\*****************************
\* Process for a truck
\*****************************
fair process truckProcess \in Trucks
begin
  TruckWaitRequest:
    while TRUE do
      await truckCommand[self].command = "request";
  TruckDrive:
      truckCommand[self].command := "arrived";
  TruckWaitStart:
      await truckCommand[self].command = "start_emptying";
  TruckEmpty:
      await binCommand[truckCommand[self].bin].command = "finished";
      binCommand[truckCommand[self].bin] := [command |-> "empty", open |-> FALSE];
  TruckAwaitEmptied:
      await binCommand[truckCommand[self].bin].command = "finished";
  TruckReport:
      truckCommand[self].command := "emptied";
    end while;
end process;

\*****************************
\* Process for the controller
\*****************************
fair process controlProcess = Control
variables
  scan = [user |-> 0, bin |-> 1],
  resp = [user |-> 0, permission |-> FALSE];
begin
  ControlLoop:
    while TRUE do
      either
        await ReadyTrucks /= {};
        truckCommand[PickReady].command := "start_emptying";
      or
        await NeedyBins /= {} /\ AvailableTrucks /= {};
        truckCommand[PickTruck] := [command |-> "request", bin |-> PickBin];
      or
        await scans /= <<>> /\ ArrivedTrucks = {} /\ ~(NeedyBins /= {} /\ AvailableTrucks /= {});
        read(scans, scan);
        write(serverRequests, [user |-> scan.user]);
  ControlAwaitServer:
        read(serverResponses, resp);
        assert resp.user = scan.user;
        if resp.permission /\ ~BinReserved(scan.bin) /\ TrashFitsCapacity(scan.bin, MaxUserTrash) then
  ControlUnlock:
          await binCommand[scan.bin].command = "finished";
          binCommand[scan.bin] := [command |-> "change_outer_lock", open |-> TRUE];
  ControlGrant:
          await binCommand[scan.bin].command = "finished";
          write(permissions[scan.user], [user |-> scan.user, bin |-> scan.bin, granted |-> TRUE]);
  ControlAwaitClosed:
          await binSensor[scan.bin].sensor = "outer_door_closed" /\ binCommand[scan.bin].command = "finished";
          binSensor[scan.bin] := [sensor |-> "idle"];
          binCommand[scan.bin] := [command |-> "change_outer_lock", open |-> FALSE];
  ControlOpenTrap:
          await binCommand[scan.bin].command = "finished";
          binCommand[scan.bin] := [command |-> "change_trap_door", open |-> TRUE];
  ControlExtendRam:
          await binCommand[scan.bin].command = "finished";
          binCommand[scan.bin] := [command |-> "change_ram", open |-> TRUE];
  ControlRetractRam:
          await binCommand[scan.bin].command = "finished";
          binCommand[scan.bin] := [command |-> "change_ram", open |-> FALSE];
  ControlCloseTrap:
          await binCommand[scan.bin].command = "finished";
          binCommand[scan.bin] := [command |-> "change_trap_door", open |-> FALSE];
        else
          write(permissions[scan.user], [user |-> scan.user, bin |-> scan.bin, granted |-> FALSE]);
        end if;
      end either;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userTrash, binCommand, binSensor, scans, permissions, 
          serverRequests, serverResponses, truckCommand, verdict, pc

(* define statement *)
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]
AvailableTrucks == {t \in Trucks : truckCommand[t].command = "emptied"}

BinFull(bin) == ~TrashFitsCapacity(bin, MaxUserTrash)
BinReserved(bin) == \E t \in Trucks : /\ truckCommand[t].bin = bin
                                      /\ truckCommand[t].command \in {"request", "arrived", "start_emptying"}
NeedyBins == {b \in Bins : BinFull(b) /\ ~BinReserved(b)}
ArrivedTrucks == {t \in Trucks : truckCommand[t].command = "arrived"}
ReadyTrucks == {t \in ArrivedTrucks : binCommand[truckCommand[t].bin].command = "finished"}
PickBin == CHOOSE b \in NeedyBins : TRUE
PickTruck == CHOOSE t \in AvailableTrucks : TRUE
PickReady == CHOOSE t \in ReadyTrucks : TRUE





TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins
          /\ \A u \in Users : verdict[u] \in BOOLEAN


MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1




CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)





OuterDoorLocked == \A b \in Bins : outerDoorLocked[b] => ~outerDoorOpen[b]

RamOuterDoor == \A b \in Bins : ramExtended[b] => (~outerDoorOpen[b] /\ outerDoorLocked[b])

TrashEmptied == \A b \in Bins : [](BinFull(b) => <>(~BinFull(b)))

UserTrash == \A u \in Users : ([]<>(userTrash[u] > 0) /\ []<>(userTrash[u] = 0))

UserTrashDeposited == \A u \in Users : [](userTrash[u] > 0 => <>(userTrash[u] = 0))

TruckEmpties == \A b \in Bins :
  [](  (\E t \in Trucks : truckCommand[t].command = "request" /\ truckCommand[t].bin = b)
       => <>(trashCompressed[b] = 0)  )

VARIABLES perm, selectedBin, req, scan, resp

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userTrash, binCommand, binSensor, scans, 
           permissions, serverRequests, serverResponses, truckCommand, 
           verdict, pc, perm, selectedBin, req, scan, resp >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = [b \in Bins |-> FALSE]
        /\ outerDoorLocked = [b \in Bins |-> TRUE]
        /\ trapDoorOpen = [b \in Bins |-> FALSE]
        /\ ramExtended = [b \in Bins |-> FALSE]
        /\ trashInTop = [b \in Bins |-> 0]
        /\ trashCompressed = [b \in Bins |-> 0]
        /\ trashUncompressed = [b \in Bins |-> 0]
        /\ trashCapacity = [b \in Bins |-> MaxCapacity]
        /\ trapDestroyed = [b \in Bins |-> FALSE]
        /\ userTrash = [u \in Users |-> 0]
        /\ binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]]
        /\ binSensor = [b \in Bins |-> [sensor |-> "idle"]]
        /\ scans = << >>
        /\ permissions = [u \in Users |-> << >>]
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]]
        /\ verdict = [u \in Users |-> FALSE]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        /\ selectedBin = [self \in Users |-> 0]
        (* Process serverProcess *)
        /\ req = [user |-> 0]
        (* Process controlProcess *)
        /\ scan = [user |-> 0, bin |-> 1]
        /\ resp = [user |-> 0, permission |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckWaitRequest"
                                        [] self = Control -> "ControlLoop"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand[self].command /= "finished"
                           /\ IF binCommand[self].command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked[self], 
                                                "Failure of assertion at line 173, column 9.")
                                      /\ outerDoorOpen' = [outerDoorOpen EXCEPT ![self] = binCommand[self].open]
                                      /\ IF ~outerDoorOpen'[self]
                                            THEN /\ binSensor' = [binSensor EXCEPT ![self] = [sensor |-> "outer_door_closed"]]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand[self].command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen[self], 
                                                           "Failure of assertion at line 180, column 9.")
                                                 /\ outerDoorLocked' = [outerDoorLocked EXCEPT ![self] = ~(binCommand[self].open)]
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand[self].command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked[self], 
                                                                      "Failure of assertion at line 183, column 9.")
                                                            /\ IF ramExtended[self] \/ CapacityExceeded(self)
                                                                  THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = [trapDoorOpen EXCEPT ![self] = binCommand[self].open]
                                                            /\ IF trapDoorOpen'[self]
                                                                  THEN /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = trashUncompressed[self] + trashInTop[self]]
                                                                       /\ trashInTop' = [trashInTop EXCEPT ![self] = 0]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand[self].command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked[self], 
                                                                                 "Failure of assertion at line 195, column 9.")
                                                                       /\ ramExtended' = [ramExtended EXCEPT ![self] = binCommand[self].open]
                                                                       /\ IF ramExtended'[self]
                                                                             THEN /\ IF ~trapDoorOpen[self]
                                                                                        THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = (trashCompressed[self]) + IF ((trashUncompressed[self]) > 1) THEN (trashUncompressed[self]) \div 2 ELSE (trashUncompressed[self])]
                                                                                  /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand[self].command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked[self], 
                                                                                            "Failure of assertion at line 207, column 9.")
                                                                                  /\ Assert(~trapDoorOpen[self], 
                                                                                            "Failure of assertion at line 208, column 9.")
                                                                                  /\ Assert(~ramExtended[self], 
                                                                                            "Failure of assertion at line 209, column 9.")
                                                                                  /\ Assert(trashInTop[self] = 0, 
                                                                                            "Failure of assertion at line 210, column 9.")
                                                                                  /\ Assert(trashUncompressed[self] = 0, 
                                                                                            "Failure of assertion at line 211, column 9.")
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 215, column 9.")
                                                                                  /\ UNCHANGED trashCompressed
                                                                       /\ UNCHANGED << ramExtended, 
                                                                                       trashUncompressed, 
                                                                                       trapDestroyed >>
                                                            /\ UNCHANGED << trapDoorOpen, 
                                                                            trashInTop >>
                                                 /\ UNCHANGED outerDoorLocked
                                      /\ UNCHANGED << outerDoorOpen, binSensor >>
                           /\ pc' = [pc EXCEPT ![self] = "BinCommandFinished"]
                           /\ UNCHANGED << trashCapacity, userTrash, 
                                           binCommand, scans, permissions, 
                                           serverRequests, serverResponses, 
                                           truckCommand, verdict, perm, 
                                           selectedBin, req, scan, resp >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT ![self].command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            binSensor, scans, permissions, 
                                            serverRequests, serverResponses, 
                                            truckCommand, verdict, perm, 
                                            selectedBin, req, scan, resp >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash[self] = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, 
                                           verdict, perm, selectedBin, req, 
                                           scan, resp >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ \E sBin \in Bins:
                           /\ selectedBin' = [selectedBin EXCEPT ![self] = sBin]
                           /\ scans' = Append(scans, ([user |-> self, bin |-> selectedBin'[self]]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, verdict, perm, req, scan, 
                                      resp >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 246, column 7.")
                               /\ Assert(perm'[self].bin = selectedBin[self], 
                                         "Failure of assertion at line 247, column 7.")
                               /\ IF perm'[self].granted
                                     THEN /\ pc' = [pc EXCEPT ![self] = "UserOpenDoor"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                               trapDoorOpen, ramExtended, 
                                               trashInTop, trashCompressed, 
                                               trashUncompressed, 
                                               trashCapacity, trapDestroyed, 
                                               userTrash, binCommand, 
                                               binSensor, scans, 
                                               serverRequests, serverResponses, 
                                               truckCommand, verdict, 
                                               selectedBin, req, scan, resp >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> TRUE]]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, verdict, perm, selectedBin, 
                                      req, scan, resp >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand[selectedBin[self]].command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, 
                                           verdict, perm, selectedBin, req, 
                                           scan, resp >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop[selectedBin[self]] = 0, 
                                    "Failure of assertion at line 254, column 9.")
                          /\ trashInTop' = [trashInTop EXCEPT ![selectedBin[self]] = userTrash[self]]
                          /\ userTrash' = [userTrash EXCEPT ![self] = 0]
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          binCommand, binSensor, scans, 
                                          permissions, serverRequests, 
                                          serverResponses, truckCommand, 
                                          verdict, perm, selectedBin, req, 
                                          scan, resp >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> FALSE]]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, verdict, perm, 
                                       selectedBin, req, scan, resp >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand[selectedBin[self]].command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             binCommand, binSensor, scans, 
                                             permissions, serverRequests, 
                                             serverResponses, truckCommand, 
                                             verdict, perm, selectedBin, req, 
                                             scan, resp >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = [userTrash EXCEPT ![self] = amt]
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, verdict, perm, selectedBin, 
                                      req, scan, resp >>

userProcess(self) == UserNextIteration(self) \/ UserScanCard(self)
                        \/ UserAwaitScanResponse(self)
                        \/ UserOpenDoor(self) \/ UserAwaitOpenDoor(self)
                        \/ UserDepositTrash(self) \/ UserCloseDoor(self)
                        \/ UserAwaitClosedDoor(self) \/ UserNewTrash(self)

ServerNextIteration == /\ pc[Server] = "ServerNextIteration"
                       /\ pc' = [pc EXCEPT ![Server] = "ServerAwaitRequest"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binCommand, binSensor, scans, 
                                       permissions, serverRequests, 
                                       serverResponses, truckCommand, verdict, 
                                       perm, selectedBin, req, scan, resp >>

ServerAwaitRequest == /\ pc[Server] = "ServerAwaitRequest"
                      /\ serverRequests /= <<>>
                      /\ req' = Head(serverRequests)
                      /\ serverRequests' = Tail(serverRequests)
                      /\ \E valid \in ValidCard(req'.user):
                           /\ serverResponses' = Append(serverResponses, ([user |-> req'.user, permission |-> valid]))
                           /\ verdict' = [verdict EXCEPT ![req'.user] = valid]
                      /\ pc' = [pc EXCEPT ![Server] = "ServerNextIteration"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      permissions, truckCommand, perm, 
                                      selectedBin, scan, resp >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckWaitRequest(self) == /\ pc[self] = "TruckWaitRequest"
                          /\ truckCommand[self].command = "request"
                          /\ pc' = [pc EXCEPT ![self] = "TruckDrive"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashInTop, trashCompressed, 
                                          trashUncompressed, trashCapacity, 
                                          trapDestroyed, userTrash, binCommand, 
                                          binSensor, scans, permissions, 
                                          serverRequests, serverResponses, 
                                          truckCommand, verdict, perm, 
                                          selectedBin, req, scan, resp >>

TruckDrive(self) == /\ pc[self] = "TruckDrive"
                    /\ truckCommand' = [truckCommand EXCEPT ![self].command = "arrived"]
                    /\ pc' = [pc EXCEPT ![self] = "TruckWaitStart"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, scans, permissions, 
                                    serverRequests, serverResponses, verdict, 
                                    perm, selectedBin, req, scan, resp >>

TruckWaitStart(self) == /\ pc[self] = "TruckWaitStart"
                        /\ truckCommand[self].command = "start_emptying"
                        /\ pc' = [pc EXCEPT ![self] = "TruckEmpty"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binCommand, binSensor, 
                                        scans, permissions, serverRequests, 
                                        serverResponses, truckCommand, verdict, 
                                        perm, selectedBin, req, scan, resp >>

TruckEmpty(self) == /\ pc[self] = "TruckEmpty"
                    /\ binCommand[truckCommand[self].bin].command = "finished"
                    /\ binCommand' = [binCommand EXCEPT ![truckCommand[self].bin] = [command |-> "empty", open |-> FALSE]]
                    /\ pc' = [pc EXCEPT ![self] = "TruckAwaitEmptied"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, verdict, perm, selectedBin, 
                                    req, scan, resp >>

TruckAwaitEmptied(self) == /\ pc[self] = "TruckAwaitEmptied"
                           /\ binCommand[truckCommand[self].bin].command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "TruckReport"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, 
                                           verdict, perm, selectedBin, req, 
                                           scan, resp >>

TruckReport(self) == /\ pc[self] = "TruckReport"
                     /\ truckCommand' = [truckCommand EXCEPT ![self].command = "emptied"]
                     /\ pc' = [pc EXCEPT ![self] = "TruckWaitRequest"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binCommand, binSensor, scans, permissions, 
                                     serverRequests, serverResponses, verdict, 
                                     perm, selectedBin, req, scan, resp >>

truckProcess(self) == TruckWaitRequest(self) \/ TruckDrive(self)
                         \/ TruckWaitStart(self) \/ TruckEmpty(self)
                         \/ TruckAwaitEmptied(self) \/ TruckReport(self)

ControlLoop == /\ pc[Control] = "ControlLoop"
               /\ \/ /\ ReadyTrucks /= {}
                     /\ truckCommand' = [truckCommand EXCEPT ![PickReady].command = "start_emptying"]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlLoop"]
                     /\ UNCHANGED <<scans, serverRequests, scan>>
                  \/ /\ NeedyBins /= {} /\ AvailableTrucks /= {}
                     /\ truckCommand' = [truckCommand EXCEPT ![PickTruck] = [command |-> "request", bin |-> PickBin]]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlLoop"]
                     /\ UNCHANGED <<scans, serverRequests, scan>>
                  \/ /\ scans /= <<>> /\ ArrivedTrucks = {} /\ ~(NeedyBins /= {} /\ AvailableTrucks /= {})
                     /\ scans /= <<>>
                     /\ scan' = Head(scans)
                     /\ scans' = Tail(scans)
                     /\ serverRequests' = Append(serverRequests, ([user |-> scan'.user]))
                     /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitServer"]
                     /\ UNCHANGED truckCommand
               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                               ramExtended, trashInTop, trashCompressed, 
                               trashUncompressed, trashCapacity, trapDestroyed, 
                               userTrash, binCommand, binSensor, permissions, 
                               serverResponses, verdict, perm, selectedBin, 
                               req, resp >>

ControlAwaitServer == /\ pc[Control] = "ControlAwaitServer"
                      /\ serverResponses /= <<>>
                      /\ resp' = Head(serverResponses)
                      /\ serverResponses' = Tail(serverResponses)
                      /\ Assert(resp'.user = scan.user, 
                                "Failure of assertion at line 327, column 9.")
                      /\ IF resp'.permission /\ ~BinReserved(scan.bin) /\ TrashFitsCapacity(scan.bin, MaxUserTrash)
                            THEN /\ pc' = [pc EXCEPT ![Control] = "ControlUnlock"]
                                 /\ UNCHANGED permissions
                            ELSE /\ permissions' = [permissions EXCEPT ![scan.user] = Append((permissions[scan.user]), ([user |-> scan.user, bin |-> scan.bin, granted |-> FALSE]))]
                                 /\ pc' = [pc EXCEPT ![Control] = "ControlLoop"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      serverRequests, truckCommand, verdict, 
                                      perm, selectedBin, req, scan >>

ControlUnlock == /\ pc[Control] = "ControlUnlock"
                 /\ binCommand[scan.bin].command = "finished"
                 /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_outer_lock", open |-> TRUE]]
                 /\ pc' = [pc EXCEPT ![Control] = "ControlGrant"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binSensor, scans, 
                                 permissions, serverRequests, serverResponses, 
                                 truckCommand, verdict, perm, selectedBin, req, 
                                 scan, resp >>

ControlGrant == /\ pc[Control] = "ControlGrant"
                /\ binCommand[scan.bin].command = "finished"
                /\ permissions' = [permissions EXCEPT ![scan.user] = Append((permissions[scan.user]), ([user |-> scan.user, bin |-> scan.bin, granted |-> TRUE]))]
                /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitClosed"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, scans, serverRequests, 
                                serverResponses, truckCommand, verdict, perm, 
                                selectedBin, req, scan, resp >>

ControlAwaitClosed == /\ pc[Control] = "ControlAwaitClosed"
                      /\ binSensor[scan.bin].sensor = "outer_door_closed" /\ binCommand[scan.bin].command = "finished"
                      /\ binSensor' = [binSensor EXCEPT ![scan.bin] = [sensor |-> "idle"]]
                      /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_outer_lock", open |-> FALSE]]
                      /\ pc' = [pc EXCEPT ![Control] = "ControlOpenTrap"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      scans, permissions, serverRequests, 
                                      serverResponses, truckCommand, verdict, 
                                      perm, selectedBin, req, scan, resp >>

ControlOpenTrap == /\ pc[Control] = "ControlOpenTrap"
                   /\ binCommand[scan.bin].command = "finished"
                   /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_trap_door", open |-> TRUE]]
                   /\ pc' = [pc EXCEPT ![Control] = "ControlExtendRam"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, userTrash, 
                                   binSensor, scans, permissions, 
                                   serverRequests, serverResponses, 
                                   truckCommand, verdict, perm, selectedBin, 
                                   req, scan, resp >>

ControlExtendRam == /\ pc[Control] = "ControlExtendRam"
                    /\ binCommand[scan.bin].command = "finished"
                    /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_ram", open |-> TRUE]]
                    /\ pc' = [pc EXCEPT ![Control] = "ControlRetractRam"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, verdict, perm, selectedBin, 
                                    req, scan, resp >>

ControlRetractRam == /\ pc[Control] = "ControlRetractRam"
                     /\ binCommand[scan.bin].command = "finished"
                     /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_ram", open |-> FALSE]]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlCloseTrap"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, verdict, perm, selectedBin, 
                                     req, scan, resp >>

ControlCloseTrap == /\ pc[Control] = "ControlCloseTrap"
                    /\ binCommand[scan.bin].command = "finished"
                    /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_trap_door", open |-> FALSE]]
                    /\ pc' = [pc EXCEPT ![Control] = "ControlLoop"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, verdict, perm, selectedBin, 
                                    req, scan, resp >>

controlProcess == ControlLoop \/ ControlAwaitServer \/ ControlUnlock
                     \/ ControlGrant \/ ControlAwaitClosed
                     \/ ControlOpenTrap \/ ControlExtendRam
                     \/ ControlRetractRam \/ ControlCloseTrap

Next == serverProcess \/ controlProcess
           \/ (\E self \in Bins: binProcess(self))
           \/ (\E self \in Users: userProcess(self))
           \/ (\E self \in Trucks: truckProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Bins : WF_vars(binProcess(self))
        /\ \A self \in Users : WF_vars(userProcess(self))
        /\ WF_vars(serverProcess)
        /\ \A self \in Trucks : WF_vars(truckProcess(self))
        /\ WF_vars(controlProcess)

\* END TRANSLATION

\* A user is in its door phase between sending "open door" and seeing the closing finished
DoorPhase == {"UserAwaitOpenDoor", "UserDepositTrash", "UserCloseDoor", "UserAwaitClosedDoor"}

\* No unauthorized user can open the outer door of any trash bin.
\* If the outer door of bin b is open, a user is in its door phase at bin b,
\* was granted permission, and the server accepted its card (ghost variable verdict).
\* Defined here because it refers to pc and the process-local variables perm and selectedBin.
AuthorizedOpenOnly ==
  \A b \in Bins : outerDoorOpen[b] =>
    \E u \in Users :
      /\ pc[u] \in DoorPhase
      /\ selectedBin[u] = b
      /\ perm[u].granted
      /\ verdict[u]

=============================================================================
\* Modification History
