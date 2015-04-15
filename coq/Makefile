CC=coqc
CFLAGS=

all: SystemFC SystemFCProp

SystemFCProp: SystemFCProp.v SystemFC
	$(CC) $(CFLAGS) SystemFCProp.v

SystemFC: SystemFC.v SfLib
	$(CC) $(CFLAGS) SystemFC.v

SfLib: SfLib.v
	$(CC) $(CFLAGS) SfLib.v

clean:
	rm *.vo *.glob
