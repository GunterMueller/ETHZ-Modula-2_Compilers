
	EXTRN	VMAP:FAR 	;Make VMAP accessible

WORKAREA SEGMENT BYTE PUBLIC 'DATA'
TOS	DW	?
NOS	DW	?
SVES	DW	?
SDX 	DW	?
WORKAREA ENDS

;**** for 1 parameter, is a function ***

UserSeg	SEGMENT BYTE PUBLIC 'PROG'

 	ASSUME	CS:UserSeg,DS:WORKAREA

PUBLIC	TestLink		;Must be public to be called externally
TestLink PROC	FAR		;Must be FAR since it is in a different code segment
        MOV	BX,DS		;Get the DS value for the interpreter
        MOV	AX,WORKAREA	;Get the DS value for this procedure
        MOV	DS,AX		;Store it into DS
        MOV	SDX,BX		;Store the old DS after current DS value has been loaded
        POP	CX		;Save the SEG and OFFSET values
        MOV	TOS,CX		;for the return to the interpreter.
        POP	CX
        MOV	NOS,CX
        POP	AX		;Get the first parameter off the stack
        CALL	VMAP		;Since it is a reference parameter, get the machine pointer to it
                 		;BX contains the offset of the parameter
                                ;AX contains the SEG value
        MOV	SVES,ES		;Save the old interpreter ES value
        MOV	ES,AX		;Load the SEG value into ES
        MOV	AX,ES:[BX]	;Get the actual value of this parameter
        MOV	CX,00H		;Assume it is not a lower case letter
        CMP	AX,141O		;Is it less than a lower case 'a'?
        JL 	TCNT
        CMP	AL,172O         ;Is it greater than a lower case 'z'?
        JG	TCNT
        SUB	AL,32		;Sub 32 to get Upper case letter
        MOV	ES:[BX],AX 	;Store in the original variable
        MOV	CX,01H		;It is TRUE that we changed the value
TCNT:
        MOV	DX,NOS		;Restore the RETurn address
        PUSH	DX
        MOV	DX,TOS
        PUSH	DX
        MOV	AX,SVES		;Restore the interpreters ES value
        MOV	ES,AX
        MOV	AX,SDX 		;Restore the interpreters DS value
        MOV	DS,AX
        MOV	AX,CX		;Functions return values in AX
        RET
TestLink	ENDP
UserSeg	ENDS
