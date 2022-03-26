import re,sys,os

filedir = sys.argv[1]
with open(filedir, "r") as f:
    fdata = f.read()

subst = [["minL_modelL", "minL"], ["GammaP_modelL", "GammaP"]]
for substpair in subst:
    oldstr = substpair[0]
    newstr = substpair[1]
    fdata = re.sub(oldstr, newstr, fdata)

with open(filedir,"w") as f:
    f.write(fdata)
    sys.exit
