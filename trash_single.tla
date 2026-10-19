---------------------------- MODULE trash_single ----------------------------

EXTENDS trash_data

(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bin
  outerDoorOpen = FALSE,
  outerDoorLocked = TRUE,
  trapDoorOpen = FALSE,
  ramExtended = FALSE,
  trashInTop = 0,
  trashCompressed = 0,
  trashUncompressed = 0,
  trashCapacity = MaxCapacity,
  trapDestroyed = FALSE,

  \* Variable for user
  userTrash = 0,

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [command |-> "finished", open |-> FALSE],
  \* Sensor from bin
  binSensor = [sensor |-> "idle"],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = << >>,
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Command for the truck
  truckCommand = [command |-> "emptied", bin |-> 1];

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity

BinFull == ~TrashFitsCapacity(MaxUserTrash)
TruckIdle == truckCommand.command = "emptied"
TruckReserved == truckCommand.command \in {"request", "arrived", "start_emptying"}

\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1

\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded

\*****************************
\* Properties of interest
\*****************************
\* The outer door can only be locked if it is closed.
OuterDoorLocked == outerDoorLocked => ~outerDoorOpen
\* The vertical ram is only used when the outer door is closed and locked.
RamOuterDoor == ramExtended => (~outerDoorOpen /\ outerDoorLocked)
\* Every time the trash bin is full, it is eventually not full anymore.
TrashEmptied == [](BinFull => <>(~BinFull))
\* The user infinitely often has trash and infinitely often has no trash.
UserTrash == []<>(userTrash > 0) /\ []<>(userTrash = 0)
\* Every time the user has trash, they can deposit their trash.
UserTrashDeposited == [](userTrash > 0 => <>(userTrash = 0))
\* Every time the truck is requested for the trash bin, the truck has eventually emptied the bin.
TruckEmpties == [](truckCommand.command = "request" => <>(trashCompressed = 0))

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
      await binCommand.command /= "finished";
      if binCommand.command = "change_outer_door" then
        \* Open/Close outer door
        assert ~outerDoorLocked;
        outerDoorOpen := binCommand.open;
        if ~outerDoorOpen then
          binSensor := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand.command = "change_outer_lock" then
        \* Lock/Unlock outer door
        assert ~outerDoorOpen;
        outerDoorLocked := ~(binCommand.open);
      elsif binCommand.command = "change_trap_door" then
        assert outerDoorLocked;
        \* Open/Close trap door
        if ramExtended \/ CapacityExceeded then
            trapDestroyed := TRUE;
        end if;
        trapDoorOpen := binCommand.open;
        if trapDoorOpen then
          \* Trash falls through
          trashUncompressed := trashUncompressed + trashInTop;
          trashInTop := 0;
        end if
      elsif binCommand.command = "change_ram" then
        assert outerDoorLocked;
        \* Extend/Retract ram
        ramExtended := binCommand.open;
        if ramExtended then
          if ~trapDoorOpen then
            trapDestroyed := TRUE;
          end if;
          \* Compress trash
          compress(trashCompressed, trashUncompressed);
        end if;
      elsif binCommand.command = "empty" then
        \* Empty trash bin
        assert outerDoorLocked;
        assert ~trapDoorOpen;
        assert ~ramExtended;
        assert trashInTop = 0;
        assert trashUncompressed = 0;
        trashCompressed := 0;
      else
        \* should not happen
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand.command := "finished";
    end while;
end process;

\*****************************
\* Process for a user
\*****************************
fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE]
begin
  UserNextIteration:
    while TRUE do
      if userTrash = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash := amt;
        end with;
      end if;
  UserScanCard:
      write(scans, [user |-> self, bin |-> 1]);
  UserAwaitScanResponse:
      read(permissions, perm);
      assert perm.user = self;
      assert perm.bin = 1;
      if perm.granted then
  UserOpenDoor:
        binCommand := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand.command = "finished";
  UserDepositTrash:
        assert trashInTop = 0;
        trashInTop := userTrash;
        userTrash := 0;
  UserCloseDoor:
        binCommand := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand.command = "finished";
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
      await truckCommand.command = "request";
  TruckDrive:
      truckCommand.command := "arrived";
  TruckWaitStart:
      await truckCommand.command = "start_emptying";
  TruckEmpty:
      await binCommand.command = "finished";
      binCommand := [command |-> "empty", open |-> FALSE];
  TruckAwaitEmptied:
      await binCommand.command = "finished";
  TruckReport:
      truckCommand.command := "emptied";
    end while;
end process;

\*****************************
\* Process for the controller
\*****************************
fair process controlProcess = Control
variables
  scan = [user |-> 0, bin |-> 0],
  resp = [user |-> 0, permission |-> FALSE];
begin
  ControlLoop:
    while TRUE do
      either
        await truckCommand.command = "arrived" /\ binCommand.command = "finished";
        truckCommand := [command |-> "start_emptying", bin |-> 1];
      or
        await TruckIdle /\ BinFull;
        truckCommand := [command |-> "request", bin |-> 1];
      or
        await scans /= <<>> /\ truckCommand.command /= "arrived" /\ ~(TruckIdle /\ BinFull);
        read(scans, scan);
        write(serverRequests, [user |-> scan.user]);
  ControlAwaitServer:
        read(serverResponses, resp);
        assert resp.user = scan.user;
        if resp.permission /\ TruckIdle /\ TrashFitsCapacity(MaxUserTrash) then
  ControlUnlock:
          await binCommand.command = "finished";
          binCommand := [command |-> "change_outer_lock", open |-> TRUE];
  ControlGrant:
          await binCommand.command = "finished";
          write(permissions, [user |-> scan.user, bin |-> scan.bin, granted |-> TRUE]);
  ControlAwaitClosed:
          await binSensor.sensor = "outer_door_closed" /\ binCommand.command = "finished";
          binSensor := [sensor |-> "idle"];
          binCommand := [command |-> "change_outer_lock", open |-> FALSE];
  ControlOpenTrap:
          await binCommand.command = "finished";
          binCommand := [command |-> "change_trap_door", open |-> TRUE];
  ControlExtendRam:
          await binCommand.command = "finished";
          binCommand := [command |-> "change_ram", open |-> TRUE];
  ControlRetractRam:
          await binCommand.command = "finished";
          binCommand := [command |-> "change_ram", open |-> FALSE];
  ControlCloseTrap:
          await binCommand.command = "finished";
          binCommand := [command |-> "change_trap_door", open |-> FALSE];
        else
          write(permissions, [user |-> scan.user, bin |-> scan.bin, granted |-> FALSE]);
        end if;
      end either;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userTrash, binCommand, binSensor, scans, permissions, 
          serverRequests, serverResponses, truckCommand, pc

(* define statement *)
Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity

BinFull == ~TrashFitsCapacity(MaxUserTrash)

TruckIdle == truckCommand.command = "emptied"
TruckReserved == truckCommand.command \in {"request", "arrived", "start_emptying"}

TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins

MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1

CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded

OuterDoorLocked == outerDoorLocked => ~outerDoorOpen

RamOuterDoor == ramExtended => (~outerDoorOpen /\ outerDoorLocked)

TrashEmptied == [](BinFull => <>(~BinFull))

UserTrash == []<>(userTrash > 0) /\ []<>(userTrash = 0)

UserTrashDeposited == [](userTrash > 0 => <>(userTrash = 0))

TruckEmpties == [](truckCommand.command = "request" => <>(trashCompressed = 0))

VARIABLES perm, req, scan, resp

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userTrash, binCommand, binSensor, scans, 
           permissions, serverRequests, serverResponses, truckCommand, pc, 
           perm, req, scan, resp >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = FALSE
        /\ outerDoorLocked = TRUE
        /\ trapDoorOpen = FALSE
        /\ ramExtended = FALSE
        /\ trashInTop = 0
        /\ trashCompressed = 0
        /\ trashUncompressed = 0
        /\ trashCapacity = MaxCapacity
        /\ trapDestroyed = FALSE
        /\ userTrash = 0
        /\ binCommand = [command |-> "finished", open |-> FALSE]
        /\ binSensor = [sensor |-> "idle"]
        /\ scans = << >>
        /\ permissions = << >>
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [command |-> "emptied", bin |-> 1]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        (* Process serverProcess *)
        /\ req = [user |-> 0]
        (* Process controlProcess *)
        /\ scan = [user |-> 0, bin |-> 0]
        /\ resp = [user |-> 0, permission |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckWaitRequest"
                                        [] self = Control -> "ControlLoop"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand.command /= "finished"
                           /\ IF binCommand.command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked, 
                                                "Failure of assertion at line 156, column 9.")
                                      /\ outerDoorOpen' = binCommand.open
                                      /\ IF ~outerDoorOpen'
                                            THEN /\ binSensor' = [sensor |-> "outer_door_closed"]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand.command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen, 
                                                           "Failure of assertion at line 163, column 9.")
                                                 /\ outerDoorLocked' = ~(binCommand.open)
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand.command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked, 
                                                                      "Failure of assertion at line 166, column 9.")
                                                            /\ IF ramExtended \/ CapacityExceeded
                                                                  THEN /\ trapDestroyed' = TRUE
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = binCommand.open
                                                            /\ IF trapDoorOpen'
                                                                  THEN /\ trashUncompressed' = trashUncompressed + trashInTop
                                                                       /\ trashInTop' = 0
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand.command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked, 
                                                                                 "Failure of assertion at line 178, column 9.")
                                                                       /\ ramExtended' = binCommand.open
                                                                       /\ IF ramExtended'
                                                                             THEN /\ IF ~trapDoorOpen
                                                                                        THEN /\ trapDestroyed' = TRUE
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = (trashCompressed + IF (trashUncompressed > 1) THEN trashUncompressed \div 2 ELSE trashUncompressed)
                                                                                  /\ trashUncompressed' = 0
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand.command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked, 
                                                                                            "Failure of assertion at line 190, column 9.")
                                                                                  /\ Assert(~trapDoorOpen, 
                                                                                            "Failure of assertion at line 191, column 9.")
                                                                                  /\ Assert(~ramExtended, 
                                                                                            "Failure of assertion at line 192, column 9.")
                                                                                  /\ Assert(trashInTop = 0, 
                                                                                            "Failure of assertion at line 193, column 9.")
                                                                                  /\ Assert(trashUncompressed = 0, 
                                                                                            "Failure of assertion at line 194, column 9.")
                                                                                  /\ trashCompressed' = 0
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 198, column 9.")
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
                                           truckCommand, perm, req, scan, resp >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT !.command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            binSensor, scans, permissions, 
                                            serverRequests, serverResponses, 
                                            truckCommand, perm, req, scan, 
                                            resp >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           req, scan, resp >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ scans' = Append(scans, ([user |-> self, bin |-> 1]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, req, scan, resp >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 224, column 7.")
                               /\ Assert(perm'[self].bin = 1, 
                                         "Failure of assertion at line 225, column 7.")
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
                                               truckCommand, req, scan, resp >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [command |-> "change_outer_door", open |-> TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, req, scan, resp >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand.command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           req, scan, resp >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop = 0, 
                                    "Failure of assertion at line 232, column 9.")
                          /\ trashInTop' = userTrash
                          /\ userTrash' = 0
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          binCommand, binSensor, scans, 
                                          permissions, serverRequests, 
                                          serverResponses, truckCommand, perm, 
                                          req, scan, resp >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [command |-> "change_outer_door", open |-> FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, perm, req, scan, resp >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand.command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             binCommand, binSensor, scans, 
                                             permissions, serverRequests, 
                                             serverResponses, truckCommand, 
                                             perm, req, scan, resp >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = amt
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, req, scan, resp >>

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
                                       serverResponses, truckCommand, perm, 
                                       req, scan, resp >>

ServerAwaitRequest == /\ pc[Server] = "ServerAwaitRequest"
                      /\ serverRequests /= <<>>
                      /\ req' = Head(serverRequests)
                      /\ serverRequests' = Tail(serverRequests)
                      /\ \E valid \in ValidCard(req'.user):
                           serverResponses' = Append(serverResponses, ([user |-> req'.user, permission |-> valid]))
                      /\ pc' = [pc EXCEPT ![Server] = "ServerNextIteration"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      permissions, truckCommand, perm, scan, 
                                      resp >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckWaitRequest(self) == /\ pc[self] = "TruckWaitRequest"
                          /\ truckCommand.command = "request"
                          /\ pc' = [pc EXCEPT ![self] = "TruckDrive"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashInTop, trashCompressed, 
                                          trashUncompressed, trashCapacity, 
                                          trapDestroyed, userTrash, binCommand, 
                                          binSensor, scans, permissions, 
                                          serverRequests, serverResponses, 
                                          truckCommand, perm, req, scan, resp >>

TruckDrive(self) == /\ pc[self] = "TruckDrive"
                    /\ truckCommand' = [truckCommand EXCEPT !.command = "arrived"]
                    /\ pc' = [pc EXCEPT ![self] = "TruckWaitStart"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, scans, permissions, 
                                    serverRequests, serverResponses, perm, req, 
                                    scan, resp >>

TruckWaitStart(self) == /\ pc[self] = "TruckWaitStart"
                        /\ truckCommand.command = "start_emptying"
                        /\ pc' = [pc EXCEPT ![self] = "TruckEmpty"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binCommand, binSensor, 
                                        scans, permissions, serverRequests, 
                                        serverResponses, truckCommand, perm, 
                                        req, scan, resp >>

TruckEmpty(self) == /\ pc[self] = "TruckEmpty"
                    /\ binCommand.command = "finished"
                    /\ binCommand' = [command |-> "empty", open |-> FALSE]
                    /\ pc' = [pc EXCEPT ![self] = "TruckAwaitEmptied"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, req, scan, resp >>

TruckAwaitEmptied(self) == /\ pc[self] = "TruckAwaitEmptied"
                           /\ binCommand.command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "TruckReport"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           req, scan, resp >>

TruckReport(self) == /\ pc[self] = "TruckReport"
                     /\ truckCommand' = [truckCommand EXCEPT !.command = "emptied"]
                     /\ pc' = [pc EXCEPT ![self] = "TruckWaitRequest"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binCommand, binSensor, scans, permissions, 
                                     serverRequests, serverResponses, perm, 
                                     req, scan, resp >>

truckProcess(self) == TruckWaitRequest(self) \/ TruckDrive(self)
                         \/ TruckWaitStart(self) \/ TruckEmpty(self)
                         \/ TruckAwaitEmptied(self) \/ TruckReport(self)

ControlLoop == /\ pc[Control] = "ControlLoop"
               /\ \/ /\ truckCommand.command = "arrived" /\ binCommand.command = "finished"
                     /\ truckCommand' = [command |-> "start_emptying", bin |-> 1]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlLoop"]
                     /\ UNCHANGED <<scans, serverRequests, scan>>
                  \/ /\ TruckIdle /\ BinFull
                     /\ truckCommand' = [command |-> "request", bin |-> 1]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlLoop"]
                     /\ UNCHANGED <<scans, serverRequests, scan>>
                  \/ /\ scans /= <<>> /\ truckCommand.command /= "arrived" /\ ~(TruckIdle /\ BinFull)
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
                               serverResponses, perm, req, resp >>

ControlAwaitServer == /\ pc[Control] = "ControlAwaitServer"
                      /\ serverResponses /= <<>>
                      /\ resp' = Head(serverResponses)
                      /\ serverResponses' = Tail(serverResponses)
                      /\ Assert(resp'.user = scan.user, 
                                "Failure of assertion at line 304, column 9.")
                      /\ IF resp'.permission /\ TruckIdle /\ TrashFitsCapacity(MaxUserTrash)
                            THEN /\ pc' = [pc EXCEPT ![Control] = "ControlUnlock"]
                                 /\ UNCHANGED permissions
                            ELSE /\ permissions' = Append(permissions, ([user |-> scan.user, bin |-> scan.bin, granted |-> FALSE]))
                                 /\ pc' = [pc EXCEPT ![Control] = "ControlLoop"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      serverRequests, truckCommand, perm, req, 
                                      scan >>

ControlUnlock == /\ pc[Control] = "ControlUnlock"
                 /\ binCommand.command = "finished"
                 /\ binCommand' = [command |-> "change_outer_lock", open |-> TRUE]
                 /\ pc' = [pc EXCEPT ![Control] = "ControlGrant"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binSensor, scans, 
                                 permissions, serverRequests, serverResponses, 
                                 truckCommand, perm, req, scan, resp >>

ControlGrant == /\ pc[Control] = "ControlGrant"
                /\ binCommand.command = "finished"
                /\ permissions' = Append(permissions, ([user |-> scan.user, bin |-> scan.bin, granted |-> TRUE]))
                /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitClosed"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, scans, serverRequests, 
                                serverResponses, truckCommand, perm, req, scan, 
                                resp >>

ControlAwaitClosed == /\ pc[Control] = "ControlAwaitClosed"
                      /\ binSensor.sensor = "outer_door_closed" /\ binCommand.command = "finished"
                      /\ binSensor' = [sensor |-> "idle"]
                      /\ binCommand' = [command |-> "change_outer_lock", open |-> FALSE]
                      /\ pc' = [pc EXCEPT ![Control] = "ControlOpenTrap"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      scans, permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, req, 
                                      scan, resp >>

ControlOpenTrap == /\ pc[Control] = "ControlOpenTrap"
                   /\ binCommand.command = "finished"
                   /\ binCommand' = [command |-> "change_trap_door", open |-> TRUE]
                   /\ pc' = [pc EXCEPT ![Control] = "ControlExtendRam"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, userTrash, 
                                   binSensor, scans, permissions, 
                                   serverRequests, serverResponses, 
                                   truckCommand, perm, req, scan, resp >>

ControlExtendRam == /\ pc[Control] = "ControlExtendRam"
                    /\ binCommand.command = "finished"
                    /\ binCommand' = [command |-> "change_ram", open |-> TRUE]
                    /\ pc' = [pc EXCEPT ![Control] = "ControlRetractRam"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, req, scan, resp >>

ControlRetractRam == /\ pc[Control] = "ControlRetractRam"
                     /\ binCommand.command = "finished"
                     /\ binCommand' = [command |-> "change_ram", open |-> FALSE]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlCloseTrap"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, perm, req, scan, resp >>

ControlCloseTrap == /\ pc[Control] = "ControlCloseTrap"
                    /\ binCommand.command = "finished"
                    /\ binCommand' = [command |-> "change_trap_door", open |-> FALSE]
                    /\ pc' = [pc EXCEPT ![Control] = "ControlLoop"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, req, scan, resp >>

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

\* An unauthorized user cannot open the outer door.
\* Defined here because it refers to the process-local variable perm.
AuthorizedOpenOnly ==
  outerDoorOpen =>
    \E u \in Users :
      /\ ValidCard(u) = {TRUE}
      /\ perm[u].granted
      /\ pc[u] \in {"UserAwaitOpenDoor", "UserDepositTrash",
                    "UserCloseDoor", "UserAwaitClosedDoor"}

=============================================================================
\* Modification History
