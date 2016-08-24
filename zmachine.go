package zmachine

import (
	"bufio"
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"math/rand"
	"os"
	"strings"
	"time"
)

type ZHeader struct {
	Version           uint8
	hiMemBase         uint16
	ip                uint16
	dictAddress       uint32
	objTableAddress   uint32
	globalVarAddress  uint32
	staticMemAddress  uint32
	abbreviationTable uint32
}

const (
	OPERAND_LARGE    = 0x0
	OPERAND_SMALL    = 0x1
	OPERAND_VARIABLE = 0x2
	OPERAND_OMITTED  = 0x3

	FORM_SHORT    = 0x0
	FORM_LONG     = 0x1
	FORM_VARIABLE = 0x2

	MAX_STACK  = 1024
	MAX_OBJECT = 256

	OBJECT_ENTRY_SIZE    = 9
	OBJECT_PARENT_INDEX  = 4
	OBJECT_SIBLING_INDEX = 5
	OBJECT_CHILD_INDEX   = 6
	NULL_OBJECT_INDEX    = 0

	DICT_NOT_FOUND = 0
)

type ZStack struct {
	stack      []uint16
	top        int
	localFrame int
}

func NewStack() *ZStack {
	s := new(ZStack)
	s.stack = make([]uint16, MAX_STACK)
	s.top = MAX_STACK
	s.localFrame = s.top

	return s
}

type ZMachine struct {
	ip          uint32
	header      ZHeader
	buf         []uint8
	stack       *ZStack
	localFrame  uint16
	Done        bool
	startState  string
	textAddress uint16
	maxChars    uint16
	TextGetter  func(func(string))
	textInput   ZTextInput
	Output      io.Writer
}

type ZTextInput struct {
	textAddress  uint16
	maxChars     uint16
	parseAddress uint32
}

type ZFunction func(*ZMachine, []uint16, uint16)
type ZFunction1Op func(*ZMachine, uint16)
type ZFunction0Op func(*ZMachine)

func DebugPrintf(format string, v ...interface{}) {
	//fmt.Printf(format, v...)
}

var alphabets = []string{"abcdefghijklmnopqrstuvwxyz",
	"ABCDEFGHIJKLMNOPQRSTUVWXYZ",
	" \n0123456789.,!?_#'\"/\\-:()"}

func (s *ZStack) Push(value uint16) {
	if s.top == 0 {
		panic("Stack overflow")
	}
	s.top--
	s.stack[s.top] = value
}

func (s *ZStack) Pop() uint16 {
	if s.top == MAX_STACK {
		panic("Trying to pop from empty stack")
	}
	retValue := s.stack[s.top]

	s.top++
	return retValue
}

func (s *ZStack) Reset(newTop int) {
	if newTop > MAX_STACK || newTop < 0 {
		panic("Invalid stack top value")
	}
	s.top = newTop
}

func (s *ZStack) GetTopItem() uint16 {
	return s.stack[s.top]
}

func (s *ZStack) SaveFrame() {
	s.Push(uint16(s.localFrame))
	s.localFrame = s.top
}

// Returns caller address (where to return to)
func (s *ZStack) RestoreFrame() uint32 {

	// Discard local frame
	s.top = s.localFrame
	// Restore previous frame
	s.localFrame = int(s.Pop())

	retLo := s.Pop()
	retHi := s.Pop()

	return (uint32(retHi) << 16) | uint32(retLo)
}

func (s *ZStack) ValidateLocalVarIndex(localVarIndex int) {
	if localVarIndex > 0xF {
		panic("Local var index out of bounds")
	}
	if s.localFrame < localVarIndex {
		panic("Stack underflow")
	}
}
func (s *ZStack) GetLocalVar(localVarIndex int) uint16 {
	s.ValidateLocalVarIndex(localVarIndex)
	stackIndex := (s.localFrame - localVarIndex) - 1
	r := s.stack[stackIndex]
	return r
}

func (s *ZStack) SetLocalVar(localVarIndex int, value uint16) {
	s.ValidateLocalVarIndex(localVarIndex)
	stackIndex := (s.localFrame - localVarIndex) - 1
	s.stack[stackIndex] = value
}

func (s *ZStack) Dump() {
	DebugPrintf("Top = %d, local frame = %d\n", s.top, s.localFrame)

	for i := MAX_STACK - 1; i >= s.top; i-- {
		if i == s.localFrame {
			DebugPrintf("0x%X: 0x%X <------ local frame\n", i, s.stack[i])
		} else {
			DebugPrintf("0x%X: 0x%X\n", i, s.stack[i])
		}
	}
}

func GetUint16(buf []byte, offset uint32) uint16 {
	return (uint16(buf[offset]) << 8) | (uint16)(buf[offset+1])
}

func GetUint32(buf []byte, offset uint32) uint32 {
	return (uint32(buf[offset]) << 24) | (uint32(buf[offset+1]) << 16) | (uint32(buf[offset+2]) << 8) | uint32(buf[offset+3])
}

func (h *ZHeader) Read(buf []byte) {

	h.Version = buf[0]
	h.hiMemBase = GetUint16(buf, 4)
	h.ip = GetUint16(buf, 6)
	h.dictAddress = uint32(GetUint16(buf, 0x8))
	h.objTableAddress = uint32(GetUint16(buf, 0xA))
	h.globalVarAddress = uint32(GetUint16(buf, 0xC))
	h.staticMemAddress = uint32(GetUint16(buf, 0xE))
	h.abbreviationTable = uint32(GetUint16(buf, 0x18))

	DebugPrintf("End of dyn mem: 0x%X\n", h.staticMemAddress)
	DebugPrintf("Global vars: 0x%X\n", h.globalVarAddress)
}

// Doesn't modify IP
func (zm *ZMachine) PeekByte() uint8 {
	return zm.buf[zm.ip]
}

// Reads & moves to the next one (advances IP)
func (zm *ZMachine) ReadByte() uint8 {
	zm.ip++
	return zm.buf[zm.ip-1]
}

// Reads 2 bytes and advances IP
func (zm *ZMachine) ReadUint16() uint16 {
	retVal := zm.GetUint16(zm.ip)
	zm.ip += 2
	return retVal
}

// We can only write to dynamic memory
func (zm *ZMachine) IsSafeToWrite(address uint32) bool {
	return address < zm.header.staticMemAddress
}

func (zm *ZMachine) GetUint16(offset uint32) uint16 {
	return (uint16(zm.buf[offset]) << 8) | (uint16)(zm.buf[offset+1])
}

func (zm *ZMachine) SetUint16(offset uint32, v uint16) {
	zm.buf[offset] = uint8(v >> 8)
	zm.buf[offset+1] = uint8(v & 0xFF)
}

// " Given a packed address P, the formula to obtain the corresponding byte address B is:
//  2P           Versions 1, 2 and 3"
func PackedAddress(a uint32) uint32 {
	return a * 2
}

func (zm *ZMachine) ReadGlobal(x uint8) uint16 {
	if x < 0x10 {
		panic("Invalid global variable")
	}

	addr := PackedAddress(uint32(x) - 0x10)
	ret := zm.GetUint16(zm.header.globalVarAddress + addr)

	return ret
}

func (zm *ZMachine) SetGlobal(x uint16, v uint16) {
	if x < 0x10 {
		panic("Invalid global variable")
	}

	addr := PackedAddress(uint32(x) - 0x10)
	zm.SetUint16(zm.header.globalVarAddress+addr, v)
}

func (zm *ZMachine) GetObjectEntryAddress(objectIndex uint16) uint32 {
	if objectIndex > MAX_OBJECT || objectIndex == 0 {
		fmt.Printf("Index: %d\n", objectIndex)
		panic("Invalid object index")
	}

	// Convert from 1-based (0 = NULL = no object) to 0-based

	objectIndex--
	// Skip default props
	objectEntryAddress := zm.header.objTableAddress + (31 * 2) + uint32(objectIndex*OBJECT_ENTRY_SIZE)

	return uint32(objectEntryAddress)
}

func (zm *ZMachine) SetObjectProperty(objectIndex uint16, propertyId uint16, value uint16) {

	objectEntryAddress := uint32(zm.GetObjectEntryAddress(objectIndex))

	propertiesAddress := GetUint16(zm.buf, objectEntryAddress+7)
	nameLength := uint16(zm.buf[propertiesAddress]) * 2 // in 2-byte words

	// Find property
	found := false
	propData := uint32(propertiesAddress + nameLength + 1)

	for !found {
		propSize := zm.buf[propData]
		if propSize == 0 {
			break
		}
		propData++
		propNo := uint16(propSize & 0x1F)

		// Props are sorted
		if propNo < propertyId {
			break
		}

		numBytes := (propSize >> 5) + 1
		if propNo == propertyId {
			found = true

			if numBytes == 1 {
				zm.buf[propData] = uint8(value & 0xFF)
			} else if numBytes == 2 {
				zm.SetUint16(propData, value)
			} else {
				panic("SetObjectProperty only supports 1/2 byte properties")
			}
		}
		propData += uint32(numBytes)
	}
	if !found {
		panic("Property not found!")
	}
}

func (zm *ZMachine) GetFirstPropertyAddress(objectIndex uint16) uint16 {
	objectEntryAddress := uint32(zm.GetObjectEntryAddress(objectIndex))
	propertiesAddress := GetUint16(zm.buf, objectEntryAddress+7)
	nameLength := uint16(zm.buf[propertiesAddress]) * 2 // in 2-byte words
	propData := propertiesAddress + nameLength + 1

	return propData
}

// Returns prop data address, number of property bytes
// (0 if not found)
func (zm *ZMachine) GetObjectPropertyInfo(objectIndex uint16, propertyId uint16) (uint16, uint16) {

	propData := zm.GetFirstPropertyAddress(objectIndex)

	// Find property
	found := false

	for !found {
		propSize := zm.buf[propData]
		if propSize == 0 {
			break
		}
		propData++
		propNo := uint16(propSize & 0x1F)

		// Props are sorted
		if propNo < propertyId {
			break
		}

		numBytes := uint16(propSize>>5) + 1
		if propNo == propertyId {
			return propData, numBytes
		}
		propData += uint16(numBytes)
	}
	return uint16(0), uint16(0)
}

func (zm *ZMachine) GetObjectPropertyAddress(objectIndex uint16, propertyId uint16) uint16 {
	address, _ := zm.GetObjectPropertyInfo(objectIndex, propertyId)
	return address
}

func (zm *ZMachine) GetNextObjectProperty(objectIndex uint16, propertyId uint16) uint16 {

	nextPropSize := uint8(0)

	// " if called with zero, it gives the first property number present."
	if propertyId == 0 {
		propData := zm.GetFirstPropertyAddress(objectIndex)
		nextPropSize = zm.buf[propData]
	} else {
		propData, numBytes := zm.GetObjectPropertyInfo(objectIndex, propertyId)
		if propData == 0 {
			panic("GetNextObjectProperty - non existent property")
		}
		nextPropSize = zm.buf[propData+numBytes]
	}
	// "zero, indicating the end of the property list"
	if nextPropSize == 0 {
		return 0
	} else {
		return uint16(nextPropSize & 0x1F)
	}
}

func (zm *ZMachine) GetObjectProperty(objectIndex uint16, propertyId uint16) uint16 {

	propData, numBytes := zm.GetObjectPropertyInfo(objectIndex, propertyId)
	result := uint16(0)

	if propData == 0 {
		// Get a default one
		result = zm.GetPropertyDefault(propertyId)
		DebugPrintf("Default prop %d = 0x%X\n", propertyId, result)
	} else {
		if numBytes == 1 {
			result = uint16(zm.buf[propData])
		} else if numBytes == 2 {
			result = GetUint16(zm.buf, uint32(propData))
		} else {
			panic("GetObjectProperty only supports 1/2 byte properties")
		}
	}

	return result
}

// True if set
func (zm *ZMachine) TestObjectAttr(objectIndex uint16, attribute uint16) bool {

	if attribute > 31 {
		panic("Attribute out of bounds")
	}

	objectEntryAddress := zm.GetObjectEntryAddress(objectIndex)

	attribs := GetUint32(zm.buf, objectEntryAddress)
	// 0: top bit
	// 31: bottom bit
	mask := uint32(1 << (31 - attribute))

	return (attribs & mask) != 0
}

func (zm *ZMachine) SetObjectAttr(objectIndex uint16, attribute uint16) {

	if attribute > 31 {
		panic("Attribute out of bounds")
	}

	objectEntryAddress := zm.GetObjectEntryAddress(objectIndex)
	byteIndex := uint32(attribute >> 3)
	shift := 7 - (attribute & 0x7)

	zm.buf[objectEntryAddress+byteIndex] |= (1 << shift)
}

func (zm *ZMachine) ClearObjectAttr(objectIndex uint16, attribute uint16) {

	if attribute > 31 {
		panic("Attribute out of bounds")
	}

	objectEntryAddress := zm.GetObjectEntryAddress(objectIndex)
	byteIndex := uint32(attribute >> 3)
	shift := 7 - (attribute & 0x7)

	zm.buf[objectEntryAddress+byteIndex] &= ^(1 << shift)
}

func (zm *ZMachine) IsDirectParent(childIndex uint16, parentIndex uint16) bool {

	return zm.GetParentObject(childIndex) == parentIndex
}

func (zm *ZMachine) GetParentObject(objectIndex uint16) uint16 {
	objectEntryAddress := zm.GetObjectEntryAddress(objectIndex)

	return uint16(zm.buf[objectEntryAddress+OBJECT_PARENT_INDEX])
}

// Unlink object from its parent
func (zm *ZMachine) UnlinkObject(objectIndex uint16) {
	objectEntryAddress := zm.GetObjectEntryAddress(objectIndex)
	currentParentIndex := uint16(zm.buf[objectEntryAddress+OBJECT_PARENT_INDEX])

	// Unlink from current parent first
	if currentParentIndex != NULL_OBJECT_INDEX {
		curParentAddress := zm.GetObjectEntryAddress(currentParentIndex)
		// If we're the first child -> move to sibling
		if uint16(zm.buf[curParentAddress+OBJECT_CHILD_INDEX]) == objectIndex {
			zm.buf[curParentAddress+OBJECT_CHILD_INDEX] = zm.buf[objectEntryAddress+OBJECT_SIBLING_INDEX]
		} else {
			childIter := uint16(zm.buf[curParentAddress+OBJECT_CHILD_INDEX])
			prevChild := uint16(NULL_OBJECT_INDEX)
			for childIter != objectIndex && childIter != NULL_OBJECT_INDEX {
				prevChild = childIter
				childIter = zm.GetSibling(childIter)
			}
			// Sanity checks
			if childIter == NULL_OBJECT_INDEX {
				panic("Object not found on parent children list")
			}
			if prevChild == NULL_OBJECT_INDEX {
				panic("Corrupted data")
			}

			prevSiblingAddress := zm.GetObjectEntryAddress(prevChild)
			sibling := zm.buf[objectEntryAddress+OBJECT_SIBLING_INDEX]
			zm.buf[prevSiblingAddress+OBJECT_SIBLING_INDEX] = sibling
		}
		zm.buf[objectEntryAddress+OBJECT_PARENT_INDEX] = NULL_OBJECT_INDEX
	}
}

func (zm *ZMachine) ReparentObject(objectIndex uint16, newParentIndex uint16) {

	objectEntryAddress := zm.GetObjectEntryAddress(objectIndex)
	currentParentIndex := uint16(zm.buf[objectEntryAddress+OBJECT_PARENT_INDEX])

	if currentParentIndex == newParentIndex {
		return
	}

	zm.UnlinkObject(objectIndex)

	// Make the first child of our new parent
	newParentAddress := zm.GetObjectEntryAddress(newParentIndex)
	zm.buf[objectEntryAddress+OBJECT_SIBLING_INDEX] = zm.buf[newParentAddress+OBJECT_CHILD_INDEX]
	zm.buf[newParentAddress+OBJECT_CHILD_INDEX] = uint8(objectIndex)
	zm.buf[objectEntryAddress+OBJECT_PARENT_INDEX] = uint8(newParentIndex)
}

func (zm *ZMachine) GetFirstChild(objectIndex uint16) uint16 {
	objectEntryAddress := zm.GetObjectEntryAddress(objectIndex)

	return uint16(zm.buf[objectEntryAddress+OBJECT_CHILD_INDEX])
}

func (zm *ZMachine) GetSibling(objectIndex uint16) uint16 {
	objectEntryAddress := zm.GetObjectEntryAddress(objectIndex)

	return uint16(zm.buf[objectEntryAddress+OBJECT_SIBLING_INDEX])
}

func (zm *ZMachine) PrintObjectName(objectIndex uint16) {
	objectEntryAddress := zm.GetObjectEntryAddress(objectIndex)
	propertiesAddress := uint32(GetUint16(zm.buf, objectEntryAddress+7))
	zm.DecodeZString(propertiesAddress + 1)
}

func ZCall(zm *ZMachine, args []uint16, numArgs uint16) {
	if numArgs == 0 {
		panic("Data corruption, call instruction requires at least 1 argument")
	}

	// Save return address
	zm.stack.Push(uint16(zm.ip>>16) & 0xFFFF)
	zm.stack.Push(uint16(zm.ip & 0xFFFF))

	functionAddress := PackedAddress(uint32(args[0]))
	DebugPrintf("Jumping to 0x%X [0x%X]\n", functionAddress, args[0])

	zm.ip = functionAddress

	// Save local frame (think EBP)
	zm.stack.SaveFrame()

	if zm.ip == 0 {
		ZReturnFalse(zm)

		return
	}

	// Local function variables on the stack
	numLocals := zm.ReadByte()

	// "When a routine is called, its local variables are created with initial values taken from the routine header.
	// Next, the arguments are written into the local variables (argument 1 into local 1 and so on)."
	numArgs-- // first argument is function address
	for i := 0; i < int(numLocals); i++ {
		localVar := zm.ReadUint16()

		if numArgs > 0 {
			localVar = args[i+1]
			numArgs--
		}
		zm.stack.Push(localVar)
	}
}

//  storew array word-index value
func ZStoreW(zm *ZMachine, args []uint16, numArgs uint16) {

	address := uint32(args[0] + args[1]*2)
	if !zm.IsSafeToWrite(address) {
		panic("Access violation")
	}

	zm.SetUint16(address, args[2])
}

func ZStoreB(zm *ZMachine, args []uint16, numArgs uint16) {

	address := uint32(args[0] + args[1])
	if !zm.IsSafeToWrite(address) {
		panic("Access violation")
	}

	zm.buf[address] = uint8(args[2])
}

func ZPutProp(zm *ZMachine, args []uint16, numArgs uint16) {
	zm.SetObjectProperty(args[0], args[1], args[2])
}

func ZRead(zm *ZMachine, args []uint16, numArgs uint16) {

	textAddress := args[0]
	maxChars := uint16(zm.buf[textAddress])
	if maxChars == 0 {
		panic("Invalid max chars")
	}
	maxChars--
	zm.wantsText(textAddress, maxChars, uint32(args[1]))
}

func (zm *ZMachine) wantsText(textAddress, maxChars uint16, parseAddress uint32) {
	zm.textInput = ZTextInput{
		textAddress:  textAddress,
		maxChars:     maxChars,
		parseAddress: parseAddress,
	}
	zm.TextGetter(zm.GotText)
}

func (zm *ZMachine) GotText(input string) {
	textAddress := zm.textInput.textAddress
	maxChars := zm.textInput.maxChars
	parseAddress := zm.textInput.parseAddress
	input = strings.ToLower(input)
	input = strings.Trim(input, "\r\n")

	copy(zm.buf[textAddress+1:textAddress+maxChars], input)
	zm.buf[textAddress+uint16(len(input))+1] = 0

	var words []string
	var wordStarts []uint16
	var stringBuffer bytes.Buffer
	prevWordStart := uint16(1)
	for i := uint16(1); zm.buf[textAddress+i] != 0; i++ {
		ch := zm.buf[textAddress+i]
		if ch == ' ' {
			if prevWordStart < 0xFFFF {
				words = append(words, stringBuffer.String())
				wordStarts = append(wordStarts, prevWordStart)
				stringBuffer.Truncate(0)
			}
			prevWordStart = 0xFFFF
		} else {
			stringBuffer.WriteByte(ch)
			if prevWordStart == 0xFFFF {
				prevWordStart = i
			}
		}
	}
	// Last word
	if prevWordStart < 0xFFFF {
		words = append(words, stringBuffer.String())
		wordStarts = append(wordStarts, prevWordStart)
	}

	// TODO: include other separators, not only spaces

	maxTokens := zm.buf[parseAddress]
	//DebugPrintf("Max tokens: %d\n", maxTokens)
	parseAddress++
	numTokens := uint8(len(words))
	if numTokens > maxTokens {
		numTokens = maxTokens
	}
	zm.buf[parseAddress] = numTokens
	parseAddress++

	// "Each block consists of the byte address of the word in the dictionary, if it is in the dictionary, or 0 if it isn't;
	// followed by a byte giving the number of letters in the word; and finally a byte giving the position in the text-buffer
	// of the first letter of the word.
	for i, w := range words {

		if uint8(i) >= maxTokens {
			break
		}

		DebugPrintf("w = %s, %d\n", w, wordStarts[i])
		dictionaryAddress := zm.FindInDictionary(w)
		DebugPrintf("Dictionary address: 0x%X\n", dictionaryAddress)

		zm.SetUint16(parseAddress, dictionaryAddress)
		zm.buf[parseAddress+2] = uint8(len(w))
		zm.buf[parseAddress+3] = uint8(wordStarts[i])
		parseAddress += 4
	}
}

func ZPrintChar(zm *ZMachine, args []uint16, numArgs uint16) {
	ch := args[0]
	PrintZChar(zm, ch)
}

func ZPrintNum(zm *ZMachine, args []uint16, numArgs uint16) {
	fmt.Fprintf(zm.Output, "%d", int16(args[0]))
}

// If range is positive, returns a uniformly random number between 1 and range.
// If range is negative, the random number generator is seeded to that value and the return value is 0.
// Most interpreters consider giving 0 as range illegal (because they attempt a division with remainder by the range),
/// but correct behaviour is to reseed the generator in as random a way as the interpreter can (e.g. by using the time
// in milliseconds).
func ZRandom(zm *ZMachine, args []uint16, numArgs uint16) {
	randRange := int16(args[0])

	if randRange > 0 {
		r := rand.Int31n(int32(randRange)) // [0, n]
		zm.StoreResult(uint16(r + 1))
	} else if randRange < 0 {
		rand.Seed(int64(randRange * -1))
		zm.StoreResult(0)
	} else {
		rand.Seed(time.Now().Unix())
		zm.StoreResult(0)
	}
}

func ZPush(zm *ZMachine, args []uint16, numArgs uint16) {
	zm.stack.Push(args[0])
}

func ZPull(zm *ZMachine, args []uint16, numArgs uint16) {
	r := zm.stack.Pop()
	DebugPrintf("Popped %d 0x%X %d %d\n", r, zm.ip, numArgs, args[0])
	zm.StoreAtLocation(args[0], r)
}

func ZNOP_VAR(zm *ZMachine, args []uint16, numArgs uint16) {
	fmt.Fprintf(zm.Output, "IP=0x%X\n", zm.ip)
	//panic("NOP VAR")
}

func ZNOP(zm *ZMachine, args []uint16) {
	fmt.Fprintf(zm.Output, "IP=0x%X\n", zm.ip)
	//panic("NOP 2OP")
}

func GenericBranch(zm *ZMachine, conditionSatisfied bool) {
	branchInfo := zm.ReadByte()

	// "If bit 7 of the first byte is 0, a branch occurs when the condition was false; if 1, then branch is on true"
	branchOnFalse := (branchInfo >> 7) == 0

	var jumpAddress int32
	var branchOffset int32
	// 0 = return false, 1 = return true, 2 = standard jump
	returnFromCurrent := int32(2)
	// "If bit 6 is set, then the branch occupies 1 byte only, and the "offset" is in the range 0 to 63, given in the bottom 6 bits"
	if (branchInfo & (1 << 6)) != 0 {
		branchOffset = int32(branchInfo & 0x3F)

		// "An offset of 0 means "return false from the current routine", and 1 means "return true from the current routine".
		if branchOffset <= 1 {
			returnFromCurrent = branchOffset
		}
	} else {
		// If bit 6 is clear, then the offset is a signed 14-bit number given in bits 0 to 5 of the first
		// byte followed by all 8 of the second.
		secondPart := zm.ReadByte()
		firstPart := uint16(branchInfo & 0x3F)
		// Propagate sign bit (2 complement)
		if (firstPart & 0x20) != 0 {
			firstPart |= (1 << 6) | (1 << 7)
		}

		branchOffset16 := int16(firstPart<<8) | int16(secondPart)
		branchOffset = int32(branchOffset16)

		DebugPrintf("Offset: 0x%X [%d]\n", branchOffset, branchOffset)
	}
	ip := int32(zm.ip)

	// "Otherwise, a branch moves execution to the instruction at address
	// Address after branch data + Offset - 2."
	jumpAddress = ip + int32(branchOffset) - 2

	DebugPrintf("Jump address = 0x%X\n", jumpAddress)

	doJump := (conditionSatisfied != branchOnFalse)

	DebugPrintf("Do jump: %t\n", doJump)

	if doJump {
		if returnFromCurrent != 2 {
			ZRet(zm, uint16(returnFromCurrent))
		} else {
			zm.ip = uint32(jumpAddress)
		}
	}
}

func ZJumpEqual(zm *ZMachine, args []uint16, numArgs uint16) {

	conditionSatisfied := (args[0] == args[1] ||
		(numArgs > 2 && args[0] == args[2]) || (numArgs > 3 && args[0] == args[3]))
	GenericBranch(zm, conditionSatisfied)
}

func ZJumpLess(zm *ZMachine, args []uint16, numArgs uint16) {
	conditionSatisfied := int16(args[0]) < int16(args[1])
	GenericBranch(zm, conditionSatisfied)
}

func ZJumpGreater(zm *ZMachine, args []uint16, numArgs uint16) {
	conditionSatisfied := int16(args[0]) > int16(args[1])
	GenericBranch(zm, conditionSatisfied)
}

func ZAdd(zm *ZMachine, args []uint16, numArgs uint16) {
	r := int16(args[0]) + int16(args[1])
	zm.StoreResult(uint16(r))
}

func ZSub(zm *ZMachine, args []uint16, numArgs uint16) {
	r := int16(args[0]) - int16(args[1])
	zm.StoreResult(uint16(r))
}

func ZMul(zm *ZMachine, args []uint16, numArgs uint16) {
	r := int16(args[0]) * int16(args[1])
	zm.StoreResult(uint16(r))
}

func ZDiv(zm *ZMachine, args []uint16, numArgs uint16) {
	if args[1] == 0 {
		panic("Division by zero")
	}

	r := int16(args[0]) / int16(args[1])
	zm.StoreResult(uint16(r))
}

func ZMod(zm *ZMachine, args []uint16, numArgs uint16) {
	if args[1] == 0 {
		panic("Division by zero (mod)")
	}

	r := int16(args[0]) % int16(args[1])
	zm.StoreResult(uint16(r))
}

func ZStore(zm *ZMachine, args []uint16, numArgs uint16) {
	DebugPrintf("%d - 0x%X\n", args[0], args[1])
	zm.StoreAtLocation(args[0], args[1])
}

func ZTestAttr(zm *ZMachine, args []uint16, numArgs uint16) {
	GenericBranch(zm, zm.TestObjectAttr(args[0], args[1]))
}

func ZOr(zm *ZMachine, args []uint16, numArgs uint16) {
	zm.StoreResult(args[0] | args[1])
}

func ZAnd(zm *ZMachine, args []uint16, numArgs uint16) {
	zm.StoreResult(args[0] & args[1])
}

func ZSetAttr(zm *ZMachine, args []uint16, numArgs uint16) {
	zm.SetObjectAttr(args[0], args[1])
}

func ZClearAttr(zm *ZMachine, args []uint16, numArgs uint16) {
	zm.ClearObjectAttr(args[0], args[1])
}

func ZLoadB(zm *ZMachine, args []uint16, numArgs uint16) {

	address := args[0] + args[1]
	value := zm.buf[address]

	zm.StoreResult(uint16(value))
}

func ZGetProp(zm *ZMachine, args []uint16, numArgs uint16) {
	prop := zm.GetObjectProperty(args[0], args[1])
	zm.StoreResult(prop)
}

func ZGetPropAddr(zm *ZMachine, args []uint16, numArgs uint16) {
	addr := zm.GetObjectPropertyAddress(args[0], args[1])
	zm.StoreResult(addr)
}

func ZGetNextProp(zm *ZMachine, args []uint16, numArgs uint16) {
	addr := zm.GetNextObjectProperty(args[0], args[1])
	zm.StoreResult(addr)
}

// array word-index -> (result)
func ZLoadW(zm *ZMachine, args []uint16, numArgs uint16) {
	address := uint32(args[0] + (args[1] * 2))
	value := GetUint16(zm.buf, address)

	zm.StoreResult(value)
}

// Returns new value.
func (zm *ZMachine) AddToVar(varType uint16, value int16) uint16 {
	retValue := uint16(0)
	if varType == 0 {
		zm.stack.stack[zm.stack.top] += uint16(value)
		retValue = zm.stack.GetTopItem()
	} else if varType < 0x10 {
		retValue = zm.stack.GetLocalVar((int)(varType - 1))
		retValue += uint16(value)
		zm.stack.SetLocalVar(int(varType-1), retValue)
	} else {
		retValue = zm.ReadGlobal(uint8(varType))
		retValue += uint16(value)
		zm.SetGlobal(varType, retValue)
	}
	return retValue
}

// dec_chk (variable) value ?(label)
// Decrement variable, and branch if it is now less than the given value.
func ZDecChk(zm *ZMachine, args []uint16, numArgs uint16) {
	newValue := zm.AddToVar(args[0], -1)
	GenericBranch(zm, int16(newValue) < int16(args[1]))
}

// inc_chk (variable) value ?(label)
// Increment variable, and branch if now greater than value.
func ZIncChk(zm *ZMachine, args []uint16, numArgs uint16) {
	newValue := zm.AddToVar(args[0], 1)
	GenericBranch(zm, int16(newValue) > int16(args[1]))
}

// test bitmap flags ?(label)
// Jump if all of the flags in bitmap are set (i.e. if bitmap & flags == flags).
func ZTest(zm *ZMachine, args []uint16, numArgs uint16) {
	bitmap := args[0]
	flags := args[1]
	GenericBranch(zm, (bitmap&flags) == flags)
}

//  jin obj1 obj2 ?(label)
// Jump if object a is a direct child of b, i.e., if parent of a is b.
func ZJin(zm *ZMachine, args []uint16, numArgs uint16) {
	GenericBranch(zm, zm.IsDirectParent(args[0], args[1]))
}

func ZInsertObj(zm *ZMachine, args []uint16, numArgs uint16) {
	zm.ReparentObject(args[0], args[1])
}

func ZJumpZero(zm *ZMachine, arg uint16) {
	GenericBranch(zm, arg == 0)
}

// get_sibling object -> (result) ?(label)
// Get next object in tree, branching if this exists, i.e. is not 0.
func ZGetSibling(zm *ZMachine, arg uint16) {
	sibling := zm.GetSibling(arg)
	zm.StoreResult(sibling)
	GenericBranch(zm, sibling != NULL_OBJECT_INDEX)
}

// get_child object -> (result) ?(label)
// Get first object contained in given object, branching if this exists, i.e. is not nothing (i.e., is not 0).
func ZGetChild(zm *ZMachine, arg uint16) {
	childIndex := zm.GetFirstChild(arg)
	zm.StoreResult(childIndex)
	GenericBranch(zm, childIndex != NULL_OBJECT_INDEX)
}

func ZGetParent(zm *ZMachine, arg uint16) {
	parent := zm.GetParentObject(arg)
	zm.StoreResult(parent)
}

func ZGetPropLen(zm *ZMachine, arg uint16) {
	if arg == 0 {
		zm.StoreResult(0)
	} else {
		// Arg = direct address of the property block
		// To get size, we need to go 1 byte back
		propSize := zm.buf[arg-1]
		numBytes := (propSize >> 5) + 1
		zm.StoreResult(uint16(numBytes))
	}
}

// print_paddr packed-address-of-string
func ZPrintPAddr(zm *ZMachine, arg uint16) {
	zm.DecodeZString(uint32(arg) * 2)
}

func ZLoad(zm *ZMachine, arg uint16) {
	zm.StoreResult(arg)
}

func ZInc(zm *ZMachine, arg uint16) {
	zm.AddToVar(arg, 1)
}

func ZDec(zm *ZMachine, arg uint16) {
	zm.AddToVar(arg, -1)
}

func ZPrintAddr(zm *ZMachine, arg uint16) {
	zm.DecodeZString(uint32(arg))
}

func ZRemoveObj(zm *ZMachine, arg uint16) {
	zm.UnlinkObject(arg)
}

func ZPrintObj(zm *ZMachine, arg uint16) {
	zm.PrintObjectName(arg)
}

func ZRet(zm *ZMachine, arg uint16) {
	returnAddress := zm.stack.RestoreFrame()
	zm.ip = returnAddress
	DebugPrintf("Returning to 0x%X\n", zm.ip)

	zm.StoreResult(arg)
}

// Unconditional jump
func ZJump(zm *ZMachine, arg uint16) {
	jumpOffset := int16(arg)
	jumpAddress := int32(zm.ip) + int32(jumpOffset) - 2
	DebugPrintf("Jump address: 0x%X\n", jumpAddress)
	zm.ip = uint32(jumpAddress)
}

func ZNOP1(zm *ZMachine, arg uint16) {
	fmt.Fprintf(zm.Output, "IP=0x%X\n", zm.ip)
	ZReturnFalse(zm)
}

func ZReturnTrue(zm *ZMachine) {
	ZRet(zm, uint16(1))
}

func ZReturnFalse(zm *ZMachine) {
	ZRet(zm, uint16(0))
}

func ZPrint(zm *ZMachine) {
	zm.ip = zm.DecodeZString(zm.ip)
}

func ZPrintRet(zm *ZMachine) {
	zm.ip = zm.DecodeZString(zm.ip)
	fmt.Fprintf(zm.Output, "\n")
	ZRet(zm, 1)
}

func ZRestart(zm *ZMachine) {
	startState := zm.startState
	zm.Deserialize(zm.startState)
	zm.startState = startState
}

func ZRetPopped(zm *ZMachine) {
	retValue := zm.stack.Pop()
	ZRet(zm, retValue)
}

func ZPop(zm *ZMachine) {
	zm.stack.Pop()
}

func ZQuit(zm *ZMachine) {
	zm.Done = true
}

func ZNewLine(zm *ZMachine) {
	fmt.Fprintf(zm.Output, "\n")
}

func ZNOP0(zm *ZMachine) {
	ZReturnFalse(zm)
}

var ZFunctions_VAR = []ZFunction{
	ZCall,
	ZStoreW,
	ZStoreB,
	ZPutProp,
	ZRead,
	ZPrintChar,
	ZPrintNum,
	ZRandom,
	ZPush,
	ZPull,
}

var ZFunctions_2OP = []ZFunction{
	ZNOP_VAR,
	ZJumpEqual,
	ZJumpLess,
	ZJumpGreater,
	ZDecChk,
	ZIncChk,
	ZJin,
	ZTest,
	ZOr,
	ZAnd,
	ZTestAttr,
	ZSetAttr,
	ZClearAttr,
	ZStore,
	ZInsertObj,
	ZLoadW,
	ZLoadB,
	ZGetProp,
	ZGetPropAddr,
	ZGetNextProp,
	ZAdd,
	ZSub,
	ZMul,
	ZDiv,
	ZMod,
}

var ZFunctions_1OP = []ZFunction1Op{
	ZJumpZero,
	ZGetSibling,
	ZGetChild,
	ZGetParent,
	ZGetPropLen,
	ZInc,
	ZDec,
	ZPrintAddr,
	ZNOP1,
	ZRemoveObj,
	ZPrintObj,
	ZRet,
	ZJump,
	ZPrintPAddr,
	ZLoad,
	ZNOP1,
}

var ZFunctions_0P = []ZFunction0Op{
	ZReturnTrue,
	ZReturnFalse,
	ZPrint,
	ZPrintRet,
	ZNOP0,
	ZNOP0,
	ZNOP0,
	ZRestart,
	ZRetPopped,
	ZPop,
	ZQuit,
	ZNewLine,
}

func (zm *ZMachine) GetOperand(operandType byte) uint16 {

	var retValue uint16

	switch operandType {
	case OPERAND_SMALL:
		retValue = uint16(zm.buf[zm.ip])
		zm.ip++
	case OPERAND_VARIABLE:
		varType := zm.buf[zm.ip]
		// 0 = top of the stack
		// 1 - 0xF = locals
		// 0x10 - 0xFF = globals
		if varType == 0 {
			retValue = zm.stack.Pop()
		} else if varType < 0x10 {
			retValue = zm.stack.GetLocalVar((int)(varType - 1))
		} else {
			retValue = zm.ReadGlobal(varType)
		}
		zm.ip++
	case OPERAND_LARGE:
		retValue = GetUint16(zm.buf, zm.ip)
		zm.ip += 2
	case OPERAND_OMITTED:
		return 0
	default:
		panic("Unknown operand type")
	}

	return retValue
}

func (zm *ZMachine) GetOperands(opTypesByte uint8, operandValues []uint16) uint16 {
	numOperands := uint16(0)
	var shift uint8
	shift = 6

	for i := 0; i < 4; i++ {
		opType := (opTypesByte >> shift) & 0x3
		shift -= 2
		if opType == OPERAND_OMITTED {
			break
		}

		opValue := zm.GetOperand(opType)
		operandValues[numOperands] = opValue
		numOperands++
	}

	return numOperands
}

func (zm *ZMachine) StoreAtLocation(storeLocation uint16, v uint16) {
	// Same deal as read variable
	// 0 = top of the stack, 0x1-0xF = local var, 0x10 - 0xFF = global var

	if storeLocation == 0 {
		zm.stack.Push(v)
	} else if storeLocation < 0x10 {
		zm.stack.SetLocalVar((int)(storeLocation-1), v)
	} else {
		zm.SetGlobal(storeLocation, v)
	}
}

func (zm *ZMachine) StoreResult(v uint16) {
	storeLocation := zm.ReadByte()

	zm.StoreAtLocation(uint16(storeLocation), v)
}

func (zm *ZMachine) InterpretVARInstruction() {

	opcode := zm.ReadByte()
	// "In variable form, if bit 5 is 0 then the count is 2OP; if it is 1, then the count is VAR.
	// The opcode number is given in the bottom 5 bits.
	instruction := (opcode & 0x1F)
	twoOp := ((opcode >> 5) & 0x1) == 0

	// "In variable or extended forms, a byte of 4 operand types is given next.
	// This contains 4 2-bit fields: bits 6 and 7 are the first field, bits 0 and 1 the fourth."
	// "A value of 0 means a small constant and 1 means a variable."
	opTypesByte := zm.ReadByte()

	opValues := make([]uint16, 4)
	numOperands := zm.GetOperands(opTypesByte, opValues)

	if twoOp {
		fn := ZFunctions_2OP[instruction]
		fn(zm, opValues, numOperands)
	} else {
		fn := ZFunctions_VAR[instruction]
		fn(zm, opValues, numOperands)
	}
}

func (zm *ZMachine) InterpretShortInstruction() {
	// "In short form, bits 4 and 5 of the opcode byte give an operand type.
	// If this is $11 then the operand count is 0OP; otherwise, 1OP. In either case the opcode number is given in the bottom 4 bits."

	opcode := zm.ReadByte()
	opType := (opcode >> 4) & 0x3
	instruction := (opcode & 0x0F)

	if opType != OPERAND_OMITTED {
		opValue := zm.GetOperand(opType)

		fn := ZFunctions_1OP[instruction]
		fn(zm, opValue)
	} else {
		fn := ZFunctions_0P[instruction]
		fn(zm)
	}
}

func (zm *ZMachine) InterpretLongInstruction() {

	opcode := zm.ReadByte()

	// In long form the operand count is always 2OP. The opcode number is given in the bottom 5 bits.
	instruction := (opcode & 0x1F)

	// Operand types:
	// In long form, bit 6 of the opcode gives the type of the first operand, bit 5 of the second.
	// A value of 0 means a small constant and 1 means a variable.
	operandType0 := ((opcode & 0x40) >> 6) + 1
	operandType1 := ((opcode & 0x20) >> 5) + 1

	opValues := make([]uint16, 2)
	opValue0 := zm.GetOperand(operandType0)
	opValue1 := zm.GetOperand(operandType1)

	opValues[0] = opValue0
	opValues[1] = opValue1

	fn := ZFunctions_2OP[instruction]
	fn(zm, opValues, 2)
}

func (zm *ZMachine) InterpretInstruction() {
	opcode := zm.PeekByte()

	DebugPrintf("IP: 0x%X - opcode: 0x%X\n", zm.ip, opcode)
	// Form is stored in top 2 bits
	// "If the top two bits of the opcode are $$11 the form is variable; if $$10, the form is short.
	// If the opcode is 190 ($BE in hexadecimal) and the version is 5 or later, the form is "extended".
	// Otherwise, the form is "long"."
	form := (opcode >> 6) & 0x3

	if form == 0x2 {
		zm.InterpretShortInstruction()
	} else if form == 0x3 {
		zm.InterpretVARInstruction()
	} else {
		zm.InterpretLongInstruction()
	}
}

// NOTE: Doesn't support abbreviations.
func (zm *ZMachine) EncodeText(txt string) uint32 {

	encodedChars := make([]uint8, 12)
	encodedWords := make([]uint16, 2)
	padding := uint8(0x5)

	// Store 6 Z-chars. Clamp if longer, add padding if shorter
	i := 0
	j := 0
	for i < 6 {
		if j < len(txt) {
			c := txt[j]
			j++

			// See if we can find any alphabet
			ai := -1
			alphabetType := 0
			for a := 0; a < len(alphabets); a++ {
				index := strings.IndexByte(alphabets[a], c)
				if index >= 0 {
					ai = index
					alphabetType = a
					break
				}
			}
			if ai >= 0 {
				if alphabetType != 0 {
					// Alphabet change
					encodedChars[i] = uint8(alphabetType + 3)
					encodedChars[i+1] = uint8(ai + 6)
					i += 2
				} else {
					encodedChars[i] = uint8(ai + 6)
					i++
				}
			} else {
				// 10-bit ZC
				encodedChars[i] = 5
				encodedChars[i+1] = 6
				encodedChars[i+2] = (c >> 5)
				encodedChars[i+3] = (c & 0x1F)
				i += 4
			}
		} else {
			// Padding
			encodedChars[i] = padding
			i++
		}
	}

	for i := 0; i < 2; i++ {
		encodedWords[i] = (uint16(encodedChars[i*3+0]) << 10) | (uint16(encodedChars[i*3+1]) << 5) |
			uint16(encodedChars[i*3+2])
		if i == 1 {
			encodedWords[i] |= 0x8000
		}
	}

	return (uint32(encodedWords[0]) << 16) | uint32(encodedWords[1])
}

func (zm *ZMachine) Initialize(buffer []uint8, header ZHeader) {
	zm.buf = buffer
	zm.header = header
	zm.ip = uint32(header.ip)
	zm.stack = NewStack()
	zm.startState = zm.Serialize()
	zm.TextGetter = func(fn func(string)) {
		reader := bufio.NewReader(os.Stdin)
		input, _ := reader.ReadString('\n')
		fn(input)
	}
	zm.Output = os.Stdout
}

type SerializableHeader struct {
	Version           uint8  `json:"version"`
	HiMemBase         uint16 `json:"hi_mem_base"`
	Ip                uint16 `json:"ip"`
	DictAddress       uint32 `json:"dict_address"`
	ObjTableAddress   uint32 `json:"obj_table_address"`
	GlobalVarAddress  uint32 `json:"global_var_address"`
	StaticMemAddress  uint32 `json:"static_mem_address"`
	AbbreviationTable uint32 `json:"abbrev_table"`
}

type SerializableStack struct {
	Stack      []uint16 `json:"stack"`
	Top        int      `json:"top"`
	LocalFrame int      `json:"local_frame"`
}

type SerializableTextInput struct {
	TextAddress  uint16 `json:"text_address"`
	MaxChars     uint16 `json:"max_chars"`
	ParseAddress uint32 `json:"parse_address"`
}

type ZMSerializer struct {
	Ip         uint32                `json:"ip"`
	Header     SerializableHeader    `json:"header"`
	Buf        []uint8               `json:"buf"`
	Stack      SerializableStack     `json:"stack"`
	LocalFrame uint16                `json:"local_frame"`
	Done       bool                  `json:"done"`
	StartState string                `json:"start_state"`
	TextInput  SerializableTextInput `json:"text_input"`
}

func (zm *ZMachine) Serialize() string {
	serializer := ZMSerializer{
		Ip: zm.ip,
		Header: SerializableHeader{
			Version:           zm.header.Version,
			HiMemBase:         zm.header.hiMemBase,
			Ip:                zm.header.ip,
			DictAddress:       zm.header.dictAddress,
			ObjTableAddress:   zm.header.objTableAddress,
			GlobalVarAddress:  zm.header.globalVarAddress,
			StaticMemAddress:  zm.header.staticMemAddress,
			AbbreviationTable: zm.header.abbreviationTable,
		},
		Buf: zm.buf,
		Stack: SerializableStack{
			Stack:      zm.stack.stack,
			Top:        zm.stack.top,
			LocalFrame: zm.stack.localFrame,
		},
		LocalFrame: zm.localFrame,
		Done:       zm.Done,
		StartState: zm.startState,
		TextInput: SerializableTextInput{
			TextAddress:  zm.textInput.textAddress,
			MaxChars:     zm.textInput.maxChars,
			ParseAddress: zm.textInput.parseAddress,
		},
	}
	bytes, _ := json.Marshal(serializer)
	return string(bytes)
}

func (zm *ZMachine) Deserialize(s string) {
	var sz ZMSerializer
	err := json.Unmarshal([]byte(s), &sz)
	if err != nil {
		return
	}
	zm.ip = sz.Ip
	zm.header = ZHeader{
		Version:           sz.Header.Version,
		hiMemBase:         sz.Header.HiMemBase,
		ip:                sz.Header.Ip,
		dictAddress:       sz.Header.DictAddress,
		objTableAddress:   sz.Header.ObjTableAddress,
		globalVarAddress:  sz.Header.GlobalVarAddress,
		staticMemAddress:  sz.Header.StaticMemAddress,
		abbreviationTable: sz.Header.AbbreviationTable,
	}
	zm.buf = sz.Buf
	zm.stack = &ZStack{
		stack:      sz.Stack.Stack,
		top:        sz.Stack.Top,
		localFrame: sz.Stack.LocalFrame,
	}
	zm.localFrame = sz.LocalFrame
	zm.Done = sz.Done
	zm.startState = sz.StartState
	zm.textInput = ZTextInput{
		textAddress:  sz.TextInput.TextAddress,
		maxChars:     sz.TextInput.MaxChars,
		parseAddress: sz.TextInput.ParseAddress,
	}
}

// Return DICT_NOT_FOUND (= 0) if not found
// Address in dictionary otherwise
func (zm *ZMachine) FindInDictionary(str string) uint16 {

	numSeparators := uint32(zm.buf[zm.header.dictAddress])
	entryLength := uint16(zm.buf[zm.header.dictAddress+1+numSeparators])
	numEntries := GetUint16(zm.buf, zm.header.dictAddress+1+numSeparators+1)

	entriesAddress := zm.header.dictAddress + 1 + numSeparators + 1 + 2

	// Dictionary entries are sorted, so we can use binary search
	lowerBound := uint16(0)
	upperBound := numEntries - 1

	encodedText := zm.EncodeText(str)

	foundAddress := uint16(DICT_NOT_FOUND)
	for lowerBound <= upperBound {

		currentIndex := lowerBound + (upperBound-lowerBound)/2
		dictValue := GetUint32(zm.buf, entriesAddress+uint32(currentIndex*entryLength))

		if encodedText < dictValue {
			upperBound = currentIndex - 1
		} else if encodedText > dictValue {
			lowerBound = currentIndex + 1
		} else {
			foundAddress = uint16(entriesAddress + uint32(currentIndex*entryLength))
			break
		}
	}

	return foundAddress
}

func (zm *ZMachine) GetPropertyDefault(propertyIndex uint16) uint16 {
	if propertyIndex < 1 || propertyIndex > 31 {
		panic("Invalid propertyIndex")
	}

	// 1-based -> 0-based
	propertyIndex--
	return GetUint16(zm.buf, zm.header.objTableAddress+uint32(propertyIndex*2))
}

func PrintZChar(zm *ZMachine, ch uint16) {
	if ch == 13 {
		fmt.Fprintf(zm.Output, "\n")
	} else if ch >= 32 && ch <= 126 { // ASCII
		fmt.Fprintf(zm.Output, "%c", ch)
	} // else ... do not bother
}

// V3 only
// Returns offset pointing just after the string data
func (zm *ZMachine) DecodeZString(startOffset uint32) uint32 {

	done := false
	zchars := []uint8{}

	i := startOffset
	for !done {

		//--first byte-------   --second byte---
		//7    6 5 4 3 2  1 0   7 6 5  4 3 2 1 0
		//bit  --first--  --second---  --third--

		w16 := GetUint16(zm.buf, i)

		done = (w16 & 0x8000) != 0
		zchars = append(zchars, uint8((w16>>10)&0x1F), uint8((w16>>5)&0x1F), uint8(w16&0x1F))

		i += 2
	}

	alphabetType := 0

	for i := 0; i < len(zchars); i++ {
		zc := zchars[i]

		// Abbreviation
		if zc > 0 && zc < 4 {
			abbrevIndex := zchars[i+1]

			// "If z is the first Z-character (1, 2 or 3) and x the subsequent one,
			// then the interpreter must look up entry 32(z-1)+x in the abbreviations table"
			abbrevAddress := GetUint16(zm.buf, zm.header.abbreviationTable+uint32(32*(zc-1)+abbrevIndex)*2)
			zm.DecodeZString(PackedAddress(uint32(abbrevAddress)))

			alphabetType = 0
			i++
			continue
		}
		if zc == 4 {
			alphabetType = 1
			continue
		} else if zc == 5 {
			alphabetType = 2
			continue
		}

		// Z-character 6 from A2 means that the two subsequent Z-characters specify a ten-bit ZSCII character code:
		// the next Z-character gives the top 5 bits and the one after the bottom 5.
		if alphabetType == 2 && zc == 6 {

			zc10 := (uint16(zchars[i+1]) << 5) | uint16(zchars[i+2])
			PrintZChar(zm, zc10)

			i += 2

			alphabetType = 0
			continue
		}

		if zc == 0 {
			fmt.Fprintf(zm.Output, " ")
		} else {
			// If we're here zc >= 6. Alphabet tables are indexed starting at 6
			aindex := zc - 6
			fmt.Fprintf(zm.Output, "%c", alphabets[alphabetType][aindex])
		}

		alphabetType = 0
	}

	return i
}

var Zork = "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ABZSAgAAAFIUdxZlAABAIHYAABZ0AkAAAFIeeRaMAABACHgAABaiAABACKeAABayAABACMefABbEAkAAAFIWfRbZAABAAHwAABb2AgAAAFJ4fxcgAAIAAH50ABcvAARADKelABc7AERAAMkAABdVCEAAAFIgohdtAAIAAPmEABeKAAIAgPmRABeYAgAAAFKvhhemAAIAAIUAABe9AEKAANwAABfQAgAIAFIciRfhAQBAAIgAABgFAgAAAFInixgkAEBAAIoAABg3AkAIAFLHjRhXAABAIIwAABhrAABAIAAAABiMAkAIAFJYkBipAARAII8AABjEAAYAAPmuABjgAARAAAAAABj6AABIQdQAABkcAgAIAFJHlRk4AABAIJQAABlHAgAAAFIwlxlsAAYAAJYAABl/AgAIAFKWmRmPAAYAAJgAABmiAgAIAFLXmxmyAADAAJpnABnFAJBAMAAAbBniAgAAAFLknhoCAAYQAJ1wABoRAQIAAMfDABooAAQQALQAoRo4AADAIKAAABpNAABQAIIAoxppAABAAKIAABqCAABAAcG3ABqXAABAAKemABq4AABAAKcAABrhBgAAAFJCqBr/AAYAAKd6ABsOAARABMoAABsgAABAAN4AABs6AABAAAAAABtaAgAAAFJkrRt1AABACKwAABuVAQIBAPmwABuxAgAAAFJg0BvBAAIAAPm2ABvUAAIAALIAABviAkAIAFIAsxv3AAIBALKxABwLAkAIAFIPtRweAAIBALSgABxHAAIAAPnNABxWAQIBAMHAABxqAAYAANfWAByBAgAAAFI0uhyRAAYAArkAAByoAgAAAFIqvBzAAABAALsAABzTAABEAOAAABz2AgAAAFIzvx0KAARQAL4AAB0hAAYAAMEAAB1HAkAIAFLJwh1YAI4QAMFubR17AAIAAMfEAB2QAAIAAMfFAB2kAAIAAMfGAB24AAIAAMcAAB3MAgAAAFKayB3iAFQQAMdbAB31AkAAAFLLyh4TADIQAMmBqR4gAkAIAFJKzB4sADIQAMsA4B5TAAAAgPnqAB5nAkAAAFJ2zx57AABAAM4AAB6SAMBQAK8A0R6pAABABNAAAB7MAABAAAAAAB7yAAHQINUAAB8FAkAIAFLc1R8nADIQANST0x86AAYAANcAAB9GAgAIAFLU2B9aAAcAANdaAB9vABQAAmYA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lKVB7wAbJZSlCPMAGzmZDUHxABs5mRBBjAAbbps0gAEAG4bBRUH3ABuG+KUI9wAbpZSlgAEAG6qUpYABABzIwKVBjQAczJSlgAEAHNO7DUGpABzXlKWAAQAc16ilIoIAHNespUGUABzX3pyAAQAc2MFZgAEAHNmUpYABABzZtUVB7AAc2p4qgAEAHUbrLiL7AB1K5iqAAQAdTNJqQakAHU26aQjvAB1RxKWAAQAdUdOFCPAAHVOo2QjwAB3XpKWAAQAd16cFIo4AHdmopUGjAB4mogUi4wAeJqVFgAEAHibjJUGOAB4q4w6AAQAeNKIFQZ0AHjTRPiLnAB408KVBjwAeOqilItUAHobdJcABkB6G3SoiygAeht04gAEAHobkpYABAB6JuViAAQAeifilgAEAHpHkpYABAB6TqwWAAQAelMClgAEAHpTCKoABAB6UwwWAAQAemeYqgAEAHp2UpYABAB7moVGAAQAe5s0NgAEAHubNLkH5AB7m4wUi6QAe6poFQZ0AHuqbLYABAB7uqWVBewAe9MFTIuIAHvTyZSLaAB764aVBkQAfR54qgAEAH0yUpcABkh9U+KWAAQAfV8ylQZMAH1fNSSK6AB9XzdMisQAfWZSlBPYAH1nmk4ABACDMqKWAAQAg05r+gAEAINOmKoABACDT7NiAAQAg19VZgAEAINffxUHuACDX7UkipwAg2KilgAEAINjBWYABACDY5KVBqQAg2aGlQe4AIaa6ZYABACGmxciAAQAhps8lQbMAIabhRUGtACGm4kWAAQAhquMlgAEAIarjOIABACGuymqAAQAhtMqlQZQAIbqiBUHwACG65UWAAQAiKpplQZEAIiqa5SLFACIurWWAAQAiLq14gAEAIi7I5UGVACI0ohwiiwAiNOFFQZYAIjTtRYABACKGxKWAAQAii63TgAEAIo7EpYABACKOzwWAAQAikdJuIvoAIpKopUGtACKSyNNBlwAik+NSQaMAIpPkzoABACKT5vQijwAims8lQZgAIpuq5YABACLmogWAAQAi5vI8gAEAIurl04ABACL04wVBmQAi/uMmIu8AI1WUpYABACNX4UVBmwAjWZSlQZoAI8jGlYABACSllKUY+hYk0pSlgAEAJNKZikGdACTSzKVBmwAk18ClIvMAJUakpSK5ACVLxNlBnAAlV5psIuoAJVii7kGo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AGwFQRGmTTgEYRh5JvRXAAVhAXFSl5ZFBFUa93gGAjRwGTb6YyEMJoSFAxE6uABsBUERpk0lyKUEOTXKLCMYEg9BKxpVVzqXAPcpSTpsBHUbWCsACmYCVElTZAEtFE8OJVcAIFb0Vu4rPgAqLdM7DTpsACdRa5ZFBCIM0msKYA06WCorAP4DChroNdMwARK0IgpnBcilBCINU2VXZM5PADXSYVEsB3gXOXE6bAAkVMjAsgQ5NcosIy6XMVll0zACCVhhU2XGRj4Bik8qKiBqp13TMdMwIyNZYAETLV6G5LIEOTXKLCMYFVzMSNk7GQRpOxUbKDVYACcbABgZNuobIAViCi5tUTm0USXIpSKOzwU9XKo4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABeXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5eXl5e"
