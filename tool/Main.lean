import FvdepCore
import FvdepIO

def main (args : List String) : IO UInt32 := FvdepIO.execute (FvdepCore.Cli.plan args)
