# Retic distinguishes between:
# - types used at function DEFINITION
# - types used as function ANNOTATIONS (higher-order)
# The annotations are "transient", the definitions are once-and-for-all
# TLDR a well-tagged program can error for some types but not others

def cast(f:Dyn)->Function([String],String):
  return f

def identity(x:Int)->Int:  # ERROR
#def identity(x): # OK
  return x

def app(f:Dyn)->String: # ERROR
#def app(f:Function([Int],Int))->String: # OK
  return cast(f)("hello")

print(app(identity))
