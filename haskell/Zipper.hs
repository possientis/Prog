type Zipper a = (Thread a, Node a)

data Branch a = KeepStraightOn a
              | TurnLeft a (Node a)
              | TurnRight a (Node a)

type Thread a = [Branch a]
