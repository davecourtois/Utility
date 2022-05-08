package Utility

import (
	"bytes"
	"crypto/md5"
	"crypto/sha1"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/ioutil"
	"log"
	"math"
	"net"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"

	"syscall"
	"time"
	"unicode"
	"unsafe"

	"image"
	"image/png"

	externalip "github.com/glendc/go-external-ip"
	"github.com/kalafut/imohash"
	"github.com/mitchellh/go-ps"
	"github.com/pborman/uuid"
	"github.com/srwiley/oksvg"
	"github.com/srwiley/rasterx"
	"github.com/txn2/txeh"

	/*"golang.org/x/sys/windows/registry"*/
	"golang.org/x/text/encoding/charmap"
	"golang.org/x/text/runes"
	"golang.org/x/text/transform"
	"golang.org/x/text/unicode/norm"
)

const (
	/*
		A JavaScript identifier must start with a letter, underscore (_), or dollar sign ($);
		subsequent characters can also be digits (0-9).
		Because JavaScript is case sensitive, letters include the characters "A"
		through "Z" (uppercase) and the characters "a" through "z" (lowercase).
	*/
	UUID_PATTERN               = "^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$"
	VARIABLE_NAME_PATTERN      = "^[a-zA-Z_$][a-zA-Z_$0-9]*$"
	PACKAGE_NAME_PATTERN       = "^[a-zA-Z_$][a-zA-Z_$0-9]*(\\.[a-zA-Z_$][a-zA-Z_$0-9]*)+(\\.[a-zA-Z_$][a-zA-Z_$0-9]*)*$"
	ENTITY_NAME_PATTERN        = "^[a-zA-Z_$][a-zA-Z_$0-9]*(\\.[a-zA-Z_$][a-zA-Z_$0-9]*)+(\\.[a-zA-Z_$][a-zA-Z_$0-9]*)*\\%[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$"
	ISO_8601_TIME_PATTERN      = `^(?P<hour>2[0-3]|[01][0-9]):(?P<minute>[0-5][0-9]):(?P<second>[0-5][0-9])(?P<ms>\.[0-9]+)?(?P<timezone>Z|[+-](?:2[0-3]|[01][0-9]):[0-5][0-9])?$`
	ISO_8601_DATE_PATTERN      = `^(?P<year>-?(?:[1-9][0-9]*)?[0-9]{4})-(?P<month>1[0-2]|0[1-9])-(?P<day>3[01]|0[1-9]|[12][0-9])$`
	ISO_8601_DATE_TIME_PATTERN = `^(?P<year>-?(?:[1-9][0-9]*)?[0-9]{4})-(?P<month>1[0-2]|0[1-9])-(?P<day>3[01]|0[1-9]|[12][0-9])T(?P<hour>2[0-3]|[01][0-9]):(?P<minute>[0-5][0-9]):(?P<second>[0-5][0-9])(?P<ms>\.[0-9]+)?(?P<timezone>Z|[+-](?:2[0-3]|[01][0-9]):[0-5][0-9])?$`
	URI_BASE_64_PATTERN        = `(data:)(\\w+)(\\/)(\\w+)(;base64)`
	STD_BASE_64_PATTERN        = `^(?:[A-Za-z0-9+/]{4})+(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?$`
)

//////////////////////////////////////////////////////////////////////////////////
// Logging to a file...
//////////////////////////////////////////////////////////////////////////////////
var (
	logChannel = make(chan string)
	logFct     func()
)

///// Note uncomment to compile on windows...

func SetEnvironmentVariable(key string, value string) error {

	return os.Setenv(key, value)

	/*
		k, err := registry.OpenKey(registry.LOCAL_MACHINE, `SYSTEM\ControlSet001\Control\Session Manager\Environment`, registry.ALL_ACCESS)
		if err != nil {
			return err
		}
		defer k.Close()

		err = k.SetStringValue(key, value)
		if err != nil {
			return err
		}
	*/
	return nil
}

func GetEnvironmentVariable(key string) (string, error) {

	return os.Getenv(key), nil

	/*
		k, err := registry.OpenKey(registry.LOCAL_MACHINE, `SYSTEM\ControlSet001\Control\Session Manager\Environment`, registry.ALL_ACCESS)
		if err != nil {
			return "", err
		}
		defer k.Close()
		var value string
		value, _, err = k.GetStringValue(key)
		if err != nil {
			return value, err
		}
		return value, nil
	*/
	return "", nil
}

func UnsetEnvironmentVariable(key string) error {

	return os.Unsetenv(key)

	/*
		k, err := registry.OpenKey(registry.LOCAL_MACHINE, `SYSTEM\ControlSet001\Control\Session Manager\Environment`, registry.ALL_ACCESS)
		if err != nil {
			return err
		}
		defer k.Close()

		err = k.DeleteValue(key)
		if err != nil {
			return err
		}
	*/
	return nil
}

func Log(infos ...interface{}) {

	// if the channel is nil that's mean no processing function is running,
	// so I will create it once.
	if logFct == nil {
		logFct = func() {
			for {
				select {
				case msg := <-logChannel:
					// Open the log file.
					f, err := os.OpenFile(os.Args[0]+".log", os.O_WRONLY|os.O_CREATE|os.O_APPEND, 0644)
					if err == nil {
						logger := log.New(f, "", log.LstdFlags)
						logger.Println(msg)
						// set the message.
						f.Close()
					}
				}
			}
		}
		go logFct()
	}

	// also display in the command prompt.
	logChannel <- fmt.Sprintln(infos)
}

/** Utility function **/
func Contains(slice []string, item string) bool {
	set := make(map[string]struct{}, len(slice))
	for _, s := range slice {
		set[s] = struct{}{}
	}

	_, ok := set[item]
	return ok
}

func Remove(s []string, index int) ([]string, error) {
	if index >= len(s) {
		return nil, errors.New("out of range Error")
	}
	return append(s[:index], s[index+1:]...), nil
}

func RemoveString(s []string, r string) []string {
	for i, v := range s {
		if v == r {
			return append(s[:i], s[i+1:]...)
		}
	}
	return s
}

//Pretty print the result.
func PrettyPrint(b []byte) ([]byte, error) {
	var out bytes.Buffer
	err := json.Indent(&out, b, "", "  ")
	return out.Bytes(), err
}

func ToJson(obj interface{}) (string, error) {
	b, err := json.Marshal(obj)
	if err != nil {
		return "", err
	}
	var b_ []byte
	b_, err = PrettyPrint(b)
	if err != nil {
		return "", err
	}

	return string(b_), nil
}

////////////////////////////////////////////////////////////////////////////////
//              			Utility function...
////////////////////////////////////////////////////////////////////////////////

/**
 * Get the list of process id by it name.
 */
func GetProcessIdsByName(name string) ([]int, error) {
	processList, err := ps.Processes()
	if err != nil {
		return nil, errors.New("ps.Processes() Failed, are you using windows?")
	}

	pids := make([]int, 0)

	// map ages
	for x := range processList {
		if strings.HasPrefix(processList[x].Executable(), name) {

			pids = append(pids, processList[x].Pid())
		}
	}

	return pids, nil
}

func PidExists(pid int) (bool, error) {
	if pid <= 0 {
		return false, fmt.Errorf("invalid pid %v", pid)
	}
	proc, err := os.FindProcess(pid)
	if err != nil {
		return false, err
	}

	if runtime.GOOS == "windows" {
		// Todo find a way to test if the process is really running...
		return true, nil
	}

	err = proc.Signal(syscall.Signal(0))
	if err == nil {
		return true, nil
	}
	if err.Error() == "os: process already finished" {
		return false, nil
	}
	errno, ok := err.(syscall.Errno)
	if !ok {
		return false, err
	}
	switch errno {
	case syscall.ESRCH:
		return false, nil
	case syscall.EPERM:
		return true, nil
	}
	return false, err
}

// check if the process is actually running
// However, on Unix systems, os.FindProcess always succeeds and returns
// a Process for the given pid...regardless of whether the process exists
// or not.
func GetProcessRunningStatus(pid int) (*os.Process, error) {
	proc, err := os.FindProcess(pid)
	if err != nil {
		return nil, err
	}

	//double check if process is running and alive
	//by sending a signal 0
	//NOTE : syscall.Signal is not available in Windows
	if runtime.GOOS == "windows" {
		return proc, nil
	}

	err = proc.Signal(syscall.Signal(0))
	if err == nil {
		return proc, nil
	}

	if err == syscall.ESRCH {
		return nil, errors.New("process not running")
	}

	// default
	return nil, errors.New("process running but query operation not permitted")
}

/**
 * Kill a process with a given name.
 */
func KillProcessByName(name string) error {
	pids, err := GetProcessIdsByName(name)
	if err != nil {
		return err
	}
	for i := 0; i < len(pids); i++ {
		proc, err := os.FindProcess(pids[i])

		if err != nil {
			log.Println(err)
		}
		//log.Println("Kill ", name, " pid ", pids[i])
		// Kill the process
		if proc != nil {
			if !strings.HasPrefix(name, "Globular") {
				err = proc.Kill()
				if err != nil {
					return err
				}
			}
		}
	}

	return nil
}

// Terminate process.
func TerminateProcess(pid int, exitcode int) error {

	/*if runtime.GOOS == "windows" {

			h, e := syscall.OpenProcess(syscall.PROCESS_TERMINATE, false, uint32(pid))
			if e != nil {
				return e
			}
			defer syscall.CloseHandle(h)

			e = syscall.TerminateProcess(h, uint32(exitcode))

		return e
	} else {*/
	p, err := os.FindProcess(pid)
	if err != nil {
		return err
	}

	return p.Signal(os.Interrupt)

	/*}*/
}

func MakeTimestamp() int64 {
	return time.Now().Unix()
}

func BytesToString(b []byte) string {
	bh := (*reflect.SliceHeader)(unsafe.Pointer(&b))
	sh := reflect.StringHeader{bh.Data, bh.Len}
	return *(*string)(unsafe.Pointer(&sh))
}

func StringToBytes(s string) []byte {
	sh := (*reflect.StringHeader)(unsafe.Pointer(&s))
	bh := reflect.SliceHeader{sh.Data, sh.Len, 0}
	return *(*[]byte)(unsafe.Pointer(&bh))
}

func DateTimeFromString(str string, layout string) (time.Time, error) {
	return time.Parse(layout, str)
}

/**
 * Parse and return a time object from a 8601 iso string, the time zone is
 * the UTC.
 */
func MatchISO8601_Time(str string) (*time.Time, error) {
	var exp = regexp.MustCompile(ISO_8601_TIME_PATTERN)
	match := exp.FindStringSubmatch(str)
	if len(match) == 0 {
		return nil, errors.New(str + " now match iso 8601")
	}
	var hour, minute, second, miliSecond int
	for i, name := range exp.SubexpNames() {
		if i != 0 {
			if name == "hour" {
				val, _ := strconv.ParseInt(match[i], 10, 64)
				hour = int(val)
			} else if name == "minute" {
				val, _ := strconv.ParseInt(match[i], 10, 64)
				minute = int(val)
			} else if name == "second" {
				val, _ := strconv.ParseInt(match[i], 10, 64)
				second = int(val)
			} else if name == "ms" {
				val, _ := strconv.ParseFloat(match[i], 64)
				miliSecond = int(val * 1000)
			}
		}
	}
	// year/mounth/day all set to zero in that case.
	t := time.Date(0, time.Month(0), 0, hour, minute, second, miliSecond, time.UTC)
	return &t, nil
}

func MatchISO8601_Date(str string) (*time.Time, error) {
	var exp = regexp.MustCompile(ISO_8601_DATE_PATTERN)
	match := exp.FindStringSubmatch(str)
	if len(match) == 0 {
		return nil, errors.New(str + " not match iso 8601")
	}
	var year, month, day int
	for i, name := range exp.SubexpNames() {
		if i != 0 {
			if name == "year" {
				val, _ := strconv.ParseInt(match[i], 10, 64)
				year = int(val)
			} else if name == "month" {
				val, _ := strconv.ParseInt(match[i], 10, 64)
				month = int(val)
			} else if name == "day" {
				val, _ := strconv.ParseInt(match[i], 10, 64)
				day = int(val)
			}
		}
	}
	t := time.Date(year, time.Month(month), day, 0, 0, 0, 0, time.UTC)
	return &t, nil
}

/**
 * Parse and return a time object from a 8601 iso string, the time zone is
 * the UTC.
 */
func MatchISO8601_DateTime(str string) (*time.Time, error) {
	var exp = regexp.MustCompile(ISO_8601_DATE_TIME_PATTERN)
	match := exp.FindStringSubmatch(str)
	if len(match) == 0 {
		return nil, errors.New(str + " not match iso 8601")
	}
	var year, month, day, hour, minute, second, miliSecond int
	for i, name := range exp.SubexpNames() {
		if i != 0 {
			if name == "year" {
				val, _ := strconv.ParseInt(match[i], 10, 64)
				year = int(val)
			} else if name == "month" {
				val, _ := strconv.ParseInt(match[i], 10, 64)
				month = int(val)
			} else if name == "day" {
				val, _ := strconv.ParseInt(match[i], 10, 64)
				day = int(val)
			} else if name == "hour" {
				val, _ := strconv.ParseInt(match[i], 10, 64)
				hour = int(val)
			} else if name == "minute" {
				val, _ := strconv.ParseInt(match[i], 10, 64)
				minute = int(val)
			} else if name == "second" {
				val, _ := strconv.ParseInt(match[i], 10, 64)
				second = int(val)
			} else if name == "ms" {
				val, _ := strconv.ParseFloat(match[i], 64)
				miliSecond = int(val * 1000)
			}
		}
	}
	t := time.Date(year, time.Month(month), day, hour, minute, second, miliSecond, time.UTC)
	return &t, nil
}

// Create a random uuid value.
func RandomUUID() string {
	return uuid.NewRandom().String()
}

// Create a MD5 hash value with UUID format.
func GenerateUUID(val string) string {
	return uuid.NewMD5(uuid.NameSpace_DNS, []byte(val)).String()
}

// Determine if a string is a UUID or not,
// a uuid is compose of a TypeName%UUID
func IsUuid(uuidStr string) bool {
	match, _ := regexp.MatchString(UUID_PATTERN, uuidStr)
	return match
}

// Determine if a string is a valid variable name
func IsValidVariableName(variableName string) bool {
	match, _ := regexp.MatchString(VARIABLE_NAME_PATTERN, variableName)
	return match
}

// Determine if a string is a valid package name
func IsValidPackageName(packageName string) bool {
	match, _ := regexp.MatchString(PACKAGE_NAME_PATTERN, packageName)
	return match
}

// Determine if a string is a valid entity reference name
func IsValidEntityReferenceName(entityReferenceName string) bool {
	match, _ := regexp.MatchString(ENTITY_NAME_PATTERN, entityReferenceName)
	return match
}

// Determine if a string is a valid base64 string
func IsStdBase64(str string) bool {
	if strings.HasPrefix(str, "/") {
		return false
	}
	match, _ := regexp.MatchString(STD_BASE_64_PATTERN, str)
	return match
}

func IsUriBase64(str string) bool {
	match, _ := regexp.MatchString(URI_BASE_64_PATTERN, str)
	return match
}

func CreateSha1Key(data []byte) string {
	h := sha1.New()
	h.Write([]byte(data))
	key := hex.EncodeToString(h.Sum(nil))
	return key
}

func GetMD5Hash(text string) string {
	hasher := md5.New()
	hasher.Write([]byte(text))
	return hex.EncodeToString(hasher.Sum(nil))
}

func RemoveAccent(text string) string {
	t := transform.Chain(norm.NFD, runes.Remove(runes.In(unicode.Mn)), norm.NFC)
	s, _, _ := transform.String(t, text)
	return s
}

/**
 * Recursive function that return the checksum value.
 */
func GetChecksum(values interface{}) string {
	var checksum string

	if reflect.TypeOf(values).String() == "map[string]interface {}" {
		var keys []string
		for k, _ := range values.(map[string]interface{}) {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for _, key := range keys {
			if values.(map[string]interface{})[key] != nil {
				checksum += GetChecksum(values.(map[string]interface{})[key])
			}
		}

	} else if reflect.TypeOf(values).String() == "[]interface {}" {

		for i := 0; i < len(values.([]interface{})); i++ {
			if values.([]interface{})[i] != nil {
				checksum += GetChecksum(values.([]interface{})[i])
			}
		}

	} else if reflect.TypeOf(values).String() == "[]map[string]interface {}" {
		for i := 0; i < len(values.([]map[string]interface{})); i++ {
			if values.([]map[string]interface{})[i] != nil {
				checksum += GetChecksum(values.([]map[string]interface{})[i])
			}
		}
	} else if reflect.TypeOf(values).String() == "[]string" {
		for i := 0; i < len(values.([]string)); i++ {
			checksum += GetChecksum(values.([]string)[i])
		}
	} else {
		// here the value must be a single value...
		checksum += ToString(values)
	}

	return GetMD5Hash(checksum)
}

// ToMap converts a struct to a map using the struct's tags.
//
// ToMap uses tags on struct fields to decide which fields to add to the
// returned map.
func ToMap(in interface{}) (map[string]interface{}, error) {
	jsonStr, err := json.Marshal(in)
	var out map[string]interface{}
	json.Unmarshal(jsonStr, &out)
	return out, err
}

const filechunk = 8192 // we settle for 8KB
func CreateFileChecksum(path string) string {
	checksum, _ := imohash.SumFile(path)
	return GetMD5Hash(string(checksum[:]))
}

func CreateDataChecksum(data []byte) string {
	checksum := imohash.Sum(data)
	return GetMD5Hash(string(checksum[:]))
}

// Exists reports whether the named file or directory exists.
func Exists(name string) bool {
	if _, err := os.Stat(name); os.IsNotExist(err) {
		// path/to/whatever does not exist
		return false
	}

	if _, err := os.Stat(name); err == nil {
		return true
	}

	return false
}

func CopyFile(source string, dest string) (err error) {

	// call a recursive copy
	cmd := exec.Command("cp", source, dest)
	var out bytes.Buffer
	var stderr bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &stderr
	err = cmd.Run()
	if err != nil {
		fmt.Println(fmt.Sprint(err) + ": " + stderr.String())
		return
	}
	fmt.Println("Result: " + out.String())
	return nil
}

func IsEmpty(name string) (bool, error) {
	f, err := os.Open(name)
	if err != nil {
		return false, err
	}
	defer f.Close()

	_, err = f.Readdirnames(1) // Or f.Readdir(1)
	if err == io.EOF {
		return true, nil
	}
	return false, err // Either not empty or error, suits both cases
}

func ReadDir(dirname string) ([]os.FileInfo, error) {
	f, err := os.Open(dirname)
	if err != nil {
		return nil, err
	}
	list, err := f.Readdir(-1)
	f.Close()
	if err != nil {
		return nil, err
	}
	sort.Slice(list, func(i, j int) bool { return list[i].Name() < list[j].Name() })
	return list, nil
}

/**
 * I made use of cp instead of go here...
 * Be sure the command exist in the computer who run that command.
 */
func CopyDir(source string, dest string) (err error) {
	// First I will create the directory
	CreateDirIfNotExist(dest)

	// call a recursive copy
	cmd := exec.Command("cp", "-R", source, dest)
	var out bytes.Buffer
	var stderr bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &stderr
	err = cmd.Run()
	if err != nil {
		fmt.Println(fmt.Sprint(err) + ": " + stderr.String())
		return
	}
	fmt.Println("Result: " + out.String())
	return nil
}

/**
 * I made use of mv instead of go here...
 * Be sure the command exist in the computer who run that command.
 */
func Move(source string, dest string) (err error) {
	// First I will create the directory
	CreateDirIfNotExist(dest)

	// call a recursive copy
	cmd := exec.Command("mv", source, dest)
	var out bytes.Buffer
	var stderr bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &stderr
	err = cmd.Run()
	if err != nil {
		fmt.Println(fmt.Sprint(err) + ": " + stderr.String())
		return
	}
	fmt.Println("Result: " + out.String())
	return nil
}

func CreateIfNotExists(dir string, perm os.FileMode) error {
	if Exists(dir) {
		return nil
	}

	if err := os.MkdirAll(dir, perm); err != nil {
		return fmt.Errorf("failed to create directory: '%s', error: '%s'", dir, err.Error())
	}

	return nil
}

func CopySymLink(source, dest string) error {
	link, err := os.Readlink(source)
	if err != nil {
		return err
	}
	return os.Symlink(link, dest)
}

func MoveFile(source, destination string) (err error) {
	src, err := os.Open(source)
	if err != nil {
		return err
	}
	defer src.Close()
	fi, err := src.Stat()
	if err != nil {
		return err
	}
	flag := os.O_WRONLY | os.O_CREATE | os.O_TRUNC
	perm := fi.Mode() & os.ModePerm
	dst, err := os.OpenFile(destination, flag, perm)
	if err != nil {
		return err
	}
	defer dst.Close()
	_, err = io.Copy(dst, src)
	if err != nil {
		dst.Close()
		os.Remove(destination)
		return err
	}
	err = dst.Close()
	if err != nil {
		return err
	}
	err = src.Close()
	if err != nil {
		return err
	}
	err = os.Remove(source)
	if err != nil {
		return err
	}
	return nil
}

func CreateDirIfNotExist(dir string) error {
	if _, err := os.Stat(dir); os.IsNotExist(err) {
		err = os.MkdirAll(dir, 0755)
		if err != nil {
			return err
		}
	}
	return nil
}

func RemoveDirContents(dir string) error {
	d, err := os.Open(dir)
	if err != nil {
		return err
	}
	defer d.Close()
	names, err := d.Readdirnames(-1)
	if err != nil {
		return err
	}
	for _, name := range names {
		err = os.RemoveAll(filepath.Join(dir, name))
		if err != nil {
			return err
		}
	}
	return nil
}

/**
 * Here I will made use of tar to compress the file.
 */
func CompressDir(src string, buf io.Writer) (int, error) {

	// First I will create the directory
	tmp := os.TempDir() + "/" + RandomUUID() + ".tgz"

	defer os.Remove(tmp)

	// Compress the directory
	cmd := exec.Command("tar", "-czvf", tmp, "-C", src, ".")
	cmd.Dir = os.TempDir()

	var out bytes.Buffer
	var stderr bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &stderr
	err := cmd.Run()
	if err != nil {
		fmt.Println(fmt.Sprint(err) + ": " + stderr.String())
		return -1, err
	}

	data, err := ioutil.ReadFile(tmp)
	if err != nil {
		return -1, err
	}

	buf.Write(data)

	return len(data), nil
}

/**
 * Extract a tar gz file and return the path where the data is...
 */
func ExtractTarGz(r io.Reader) (string, error) {

	// First I will create the directory
	tmp := RandomUUID() + ".tgz"
	//defer os.Remove(tmp)

	// Now the buffer contain the .tgz data
	buf, err := ioutil.ReadAll(r)
	if err != nil {
		return "", err
	}

	// Here I will write the data into a tgz file...
	err = ioutil.WriteFile(os.TempDir()+"/"+tmp, buf, 0777)
	if err != nil {
		return "", err
	}
	prevDir, _ := os.Getwd()
	os.Chdir(os.TempDir())
	defer os.Chdir(prevDir)

	// Untar into the output dir and return it path.
	output := RandomUUID()
	CreateDirIfNotExist(os.TempDir() + "/" + output)

	cmd := exec.Command("tar", "-xvzf", tmp, "-C", output, "--strip-components", "1")
	cmd.Dir = os.TempDir()
	log.Println("extract file: tar -xvzf ", tmp)
	var out bytes.Buffer
	var stderr bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &stderr
	err = cmd.Run()
	if err != nil {
		fmt.Println(fmt.Sprint(err) + ": " + stderr.String())
		return "", err
	}

	return os.TempDir() + "/" + output, nil
}

func FindFileByName(path string, name string) ([]string, error) {
	files := make([]string, 0)
	err := filepath.Walk(path, func(path string, info os.FileInfo, err error) error {
		if strings.HasPrefix(name, ".") {
			if err == nil && strings.HasSuffix(info.Name(), name) {
				files = append(files, path)
			}
		} else if err == nil && info.Name() == name {
			files = append(files, path)
		}
		return err
	})
	return files, err
}

// copyFileContents copies the contents of the file named src to the file named
// by dst. The file will be created if it does not already exist. If the
// destination file exists, all it's contents will be replaced by the contents
// of the source file.
func copyFileContents(src, dst string) (err error) {
	in, err := os.Open(src)
	if err != nil {
		return
	}
	defer in.Close()
	out, err := os.Create(dst)
	if err != nil {
		return
	}
	defer func() {
		cerr := out.Close()
		if err == nil {
			err = cerr
		}
	}()
	if _, err = io.Copy(out, in); err != nil {
		return
	}
	err = out.Sync()
	return
}

func FileLine() string {
	_, fileName, fileLine, ok := runtime.Caller(1)
	var s string
	if ok {
		s = fmt.Sprintf("%s:%d", fileName, fileLine)
	} else {
		s = ""
	}
	return s
}

func FunctionName() string {
	pc := make([]uintptr, 10) // at least 1 entry needed
	runtime.Callers(2, pc)
	f := runtime.FuncForPC(pc[0])
	return f.Name()
}

func JsonErrorStr(functionName string, fileLine string, err error) string {
	str, _ := json.Marshal(map[string]string{"FunctionName": functionName, "FileLine": fileLine, "ErrorMsg": err.Error()})
	return string(str)
}

/**
 * Insert a new string at a given position.
 */
func InsertStringAt(pos int, str string, arr *[]string) {
	*arr = append(*arr, "")
	for i := len(*arr) - 1; i > pos; i-- {
		(*arr)[i] = (*arr)[i-1]
	}
	(*arr)[pos] = str
}

func InsertIntAt(pos int, val int, arr *[]int) {
	*arr = append(*arr, 0)
	for i := len(*arr) - 1; i > pos; i-- {
		(*arr)[i] = (*arr)[i-1]
	}
	(*arr)[pos] = val
}

func InsertInt64At(pos int, val int64, arr *[]int64) {
	*arr = append(*arr, 0)
	for i := len(*arr) - 1; i > pos; i-- {
		(*arr)[i] = (*arr)[i-1]
	}
	(*arr)[pos] = val
}

func InsertBoolAt(pos int, val bool, arr *[]bool) {
	*arr = append(*arr, false)
	for i := len(*arr) - 1; i > pos; i-- {
		(*arr)[i] = (*arr)[i-1]
	}
	(*arr)[pos] = val
}

// IPInfo describes a particular IP address.
type IPInfo struct {
	// IP holds the described IP address.
	IP string
	// Hostname holds a DNS name associated with the IP address.
	Hostname string
	// City holds the city of the ISP location.
	City string
	// Country holds the two-letter country code.
	Country string
	// Loc holds the latitude and longitude of the
	// ISP location as a comma-separated northing, easting
	// pair of floating point numbers.
	Loc string
	// Org describes the organization that is
	// responsible for the IP address.
	Org string
	// Postal holds the post code or zip code region of the ISP location.
	Postal string
}

// getMacAddr gets the MAC hardware
// address of the host machine
func MyMacAddr(ip string) (string, error) {

	addrs, err := net.InterfaceAddrs()
	if err != nil {
		return "", err
	}

	var currentIP, currentNetworkHardwareName string

	for _, address := range addrs {

		// check the address type and if it is not a loopback the display it
		// = GET LOCAL IP ADDRESS
		if ipnet, ok := address.(*net.IPNet); ok && !ipnet.IP.IsLoopback() {
			if ipnet.IP.To4() != nil {
				currentIP = ipnet.IP.String()
				if currentIP == ip {
					break // the ip was found...
				}
			}
		}
	}

	// get all the system's or local machine's network interfaces
	interfaces, _ := net.Interfaces()
	for _, interf := range interfaces {

		if addrs, err := interf.Addrs(); err == nil {
			for /*index*/_ , addr := range addrs {
				//fmt.Println("[", index, "]", interf.Name, ">", addr)

				// only interested in the name with current IP address
				if strings.Contains(addr.String(), currentIP) {
					currentNetworkHardwareName = interf.Name
				}
			}
		}
	}

	// extract the hardware information base on the interface name
	// capture above
	netInterface, err := net.InterfaceByName(currentNetworkHardwareName)
	if err != nil {
		return "", err
	}

	macAddress := netInterface.HardwareAddr

	return macAddress.String(), nil
}

func DomainHasIp(domain string, ip string) bool {
	// I will wait until the same ip is return from the dns lookup.
	ips, err := net.LookupIP(domain)
	if err != nil {
		return false
	}

	for i := 0; i < len(ips); i++ {
		ip_ := ips[i]
		if ip_.String() == ip {
			return true
		}
	}

	return false
}

// Return the external ip.
func MyIP() string {

	consensus := externalip.DefaultConsensus(&externalip.ConsensusConfig{Timeout: 500 * time.Millisecond}, nil)
	// Get your IP,
	// which is never <nil> when err is <nil>.
	ip, err := consensus.ExternalIP()
	if err == nil {
		return ip.String() // print IPv4/IPv6 in string format
	}
	return ""
}

// Return the local ip.
func MyLocalIP() string {

	// GetLocalIP returns the non loopback local IP of the host
	addrs, err := net.InterfaceAddrs()
	if err != nil {
		return ""
	}
	for _, address := range addrs {
		// check the address type and if it is not a loopback the display it
		if ipnet, ok := address.(*net.IPNet); ok && !ipnet.IP.IsLoopback() {
			if ipnet.IP.To4() != nil {
				//return ipnet.IP.String()
				ip := ipnet.IP.String()
				// reject Automatic Private IP address
				// TODO 
				if !strings.HasPrefix(ip, "169.254.") && (strings.HasPrefix(ip, "192.168.") || strings.HasPrefix(ip, "10.")){
					//fmt.Println("-------> local ip is ", ip)
					return ip
				}
			}
		}
	}
	return ""
}

// Check if a ip is private.
func privateIPCheck(ip string) bool {
	ipAddress := net.ParseIP(ip)
	return ipAddress.IsPrivate()
}

// Get the ip from an address
func GetIpv4(address string) (string, error) {
	// remove the port number from the address
	if strings.Contains(address, ":") {
		address = address[0:strings.Index(address, ":")]
	}

	// Test if the hostname is in the /etc/hosts file...
	hosts, err := txeh.NewHostsDefault()
	if err != nil {
		return "", err
	}

	exist, ip, _ := hosts.HostAddressLookup(address)
	if exist {
		return ip, nil
	}

	// I will try to resolve the address from...
	ips, _ := net.LookupIP(address)
	for _, ip := range ips {
		if ipv4 := ip.To4(); ipv4 != nil {
			return ipv4.String(), nil
		}
	}

	return "", errors.New("no address found for domain " + address)
}

func IsLocal(hostname string) bool {

	// remove the port number from the address
	if strings.Contains(hostname, ":") {
		hostname = hostname[0:strings.Index(hostname, ":")]
	}

	// Test if the hostname is in the /etc/hosts file...
	hosts, err := txeh.NewHostsDefault()
	if err != nil {
		return false
	}

	exist, ip, _ := hosts.HostAddressLookup(hostname)
	if exist {
		isLocal := privateIPCheck(ip)
		return isLocal
	}

	return false
}

// ForeignIP provides information about the given IP address,
// which should be in dotted-quad form.
func ForeignIP(ip string) (*IPInfo, error) {
	if ip != "" {
		ip += "/" + ip
	}
	response, err := http.Get("http://ipinfo.io" + ip + "/json")
	if err != nil {
		return nil, err
	}
	defer response.Body.Close()

	contents, err := ioutil.ReadAll(response.Body)
	if err != nil {
		return nil, err
	}
	var ipinfo IPInfo
	if err := json.Unmarshal(contents, &ipinfo); err != nil {
		return nil, err
	}
	return &ipinfo, nil
}

// Various decoding function.

// Windows1250
func DecodeWindows1250(val string) (string, error) {

	b := []byte(val)
	dec := charmap.Windows1250.NewDecoder()

	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// Windows1251
func DecodeWindows1251(val string) (string, error) {

	b := []byte(val)
	dec := charmap.Windows1251.NewDecoder()

	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// Windows1252
func DecodeWindows1252(val string) (string, error) {

	b := []byte(val)
	dec := charmap.Windows1252.NewDecoder()

	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// Windows1253
func DecodeWindows1253(val string) (string, error) {

	b := []byte(val)
	dec := charmap.Windows1253.NewDecoder()

	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// Windows1254
func DecodeWindows1254(val string) (string, error) {

	b := []byte(val)
	dec := charmap.Windows1254.NewDecoder()

	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// Windows1255
func DecodeWindows1255(val string) (string, error) {

	b := []byte(val)
	dec := charmap.Windows1255.NewDecoder()

	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// Windows1256
func DecodeWindows1256(val string) (string, error) {

	b := []byte(val)
	dec := charmap.Windows1256.NewDecoder()

	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// Windows1257
func DecodeWindows1257(val string) (string, error) {

	b := []byte(val)
	dec := charmap.Windows1257.NewDecoder()

	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// Windows1258
func DecodeWindows1258(val string) (string, error) {

	b := []byte(val)
	dec := charmap.Windows1258.NewDecoder()

	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_1
func DecodeISO8859_1(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_1.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_2
func DecodeISO8859_2(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_2.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_3
func DecodeISO8859_3(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_3.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_4
func DecodeISO8859_4(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_4.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_5
func DecodeISO8859_5(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_5.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_6
func DecodeISO8859_6(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_6.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_7
func DecodeISO8859_7(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_7.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_8
func DecodeISO8859_8(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_8.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_9
func DecodeISO8859_9(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_9.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_10
func DecodeISO8859_10(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_10.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_13
func DecodeISO8859_13(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_13.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_14
func DecodeISO8859_14(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_14.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_15
func DecodeISO8859_15(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_15.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// ISO8859_16
func DecodeISO8859_16(val string) (string, error) {

	b := []byte(val)
	dec := charmap.ISO8859_16.NewDecoder()
	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// KOI8R
func DecodeKOI8R(val string) (string, error) {

	b := []byte(val)
	dec := charmap.KOI8R.NewDecoder()

	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

// KOI8U
func DecodeKOI8U(val string) (string, error) {

	b := []byte(val)
	dec := charmap.KOI8U.NewDecoder()

	// Take more space just in case some characters need
	// more bytes in UTF-8 than in Win1256.
	bUTF := make([]byte, len(b)*3)
	n, _, err := dec.Transform(bUTF, b, false)
	if err != nil {
		return "", err
	}

	bUTF = bUTF[:n]
	return string(bUTF), nil
}

/**
 * Convert a numerical value to a string.
 */
func ToString(value interface{}) string {
	var str string
	if reflect.TypeOf(value).Kind() == reflect.String {
		str += value.(string)
	} else if reflect.TypeOf(value).Kind() == reflect.Int {
		str += strconv.Itoa(toInt(value))
	} else if reflect.TypeOf(value).Kind() == reflect.Int8 {
		str += strconv.Itoa(int(value.(int8)))
	} else if reflect.TypeOf(value).Kind() == reflect.Int16 {
		str += strconv.Itoa(int(value.(int16)))
	} else if reflect.TypeOf(value).Kind() == reflect.Int32 {
		str += strconv.Itoa(int(value.(int32)))
	} else if reflect.TypeOf(value).Kind() == reflect.Int64 {
		str += strconv.Itoa(int(value.(int64)))
	} else if reflect.TypeOf(value).Kind() == reflect.Uint8 {
		str += strconv.Itoa(int(value.(uint8)))
	} else if reflect.TypeOf(value).Kind() == reflect.Uint16 {
		str += strconv.Itoa(int(value.(uint16)))
	} else if reflect.TypeOf(value).Kind() == reflect.Uint32 {
		str += strconv.Itoa(int(value.(uint32)))
	} else if reflect.TypeOf(value).Kind() == reflect.Uint64 {
		str += strconv.Itoa(int(value.(uint64)))
	} else if reflect.TypeOf(value).Kind() == reflect.Float32 {
		str += strconv.FormatFloat(float64(value.(float32)), 'f', -1, 32)
	} else if reflect.TypeOf(value).Kind() == reflect.Float64 {
		str += strconv.FormatFloat(value.(float64), 'f', -1, 64)
	} else if reflect.TypeOf(value).Kind() == reflect.Bool {
		str += strconv.FormatBool(value.(bool))
	} else if reflect.TypeOf(value).String() == "[]uint8" {
		str += string(value.([]uint8))
	} else if reflect.TypeOf(value).String() == "*errors.errorString" || reflect.TypeOf(value).String() == "*errors.Error" {
		errStr := value.(error).Error()
		str += errStr
	} else if reflect.TypeOf(value).String() == "[]string" {
		for i := 0; i < len(value.([]string)); i++ {
			str += value.([]string)[i]
			if i < len(value.([]string))-1 {
				str += " "
			}
		}
	} else if reflect.TypeOf(value).String() == "map[string]interface {}" {
		data, err := json.Marshal(value)
		if err == nil {
			return string(data)
		} else {
			return "{}"
		}
	} else {
		log.Panicln("Value with type:", reflect.TypeOf(value).String(), "cannot be convert to string")
	}
	// Remove leading space.
	return strings.TrimSpace(str)
}

func ToInt(value interface{}) int {
	if value == nil {
		return 0
	}

	var val int
	if reflect.TypeOf(value).Kind() == reflect.String {
		val, _ = strconv.Atoi(value.(string))
	} else if reflect.TypeOf(value).Kind() == reflect.Int {
		val = value.(int)
	} else if reflect.TypeOf(value).Kind() == reflect.Int8 {
		val = int(value.(int8))
	} else if reflect.TypeOf(value).Kind() == reflect.Int16 {
		val = int(value.(int16))
	} else if reflect.TypeOf(value).Kind() == reflect.Int32 {
		val = int(value.(int32))
	} else if reflect.TypeOf(value).Kind() == reflect.Int64 {
		val = int(value.(int64))
	} else if reflect.TypeOf(value).Kind() == reflect.Float32 {
		val = int(value.(float32))
	} else if reflect.TypeOf(value).Kind() == reflect.Float64 {
		val = int(value.(float64))
	} else if reflect.TypeOf(value).Kind() == reflect.Bool {
		if value.(bool) {
			val = 1
		} else {
			val = 0
		}
	} else if reflect.TypeOf(value).String() == "[]uint8" {
		val = int(binary.BigEndian.Uint64(value.([]uint8)))
	} else {
		log.Panicln("Value with type:", reflect.TypeOf(value).String(), "cannot be convert to integer value")
	}
	return val
}

func IsBool(value interface{}) bool {
	if reflect.TypeOf(value).Kind() == reflect.Bool {
		return true
	} else if reflect.TypeOf(value).Kind() == reflect.String {
		_, err := strconv.ParseBool(value.(string))
		if err != nil {
			return false
		} else {
			return true
		}
	}
	return false
}

func ToBool(value interface{}) bool {
	if reflect.TypeOf(value).Kind() == reflect.Bool {
		return value.(bool)
	} else if reflect.TypeOf(value).Kind() == reflect.String {
		value_, err := strconv.ParseBool(value.(string))
		if err != nil {
			return false
		} else {
			return value_
		}
	}
	return false
}

func IsNumeric(value interface{}) bool {

	if reflect.TypeOf(value).Kind() == reflect.String {
		return false
	} else if reflect.TypeOf(value).Kind() == reflect.Int {
		return true
	} else if reflect.TypeOf(value).Kind() == reflect.Int8 {
		return true
	} else if reflect.TypeOf(value).Kind() == reflect.Int16 {
		return true
	} else if reflect.TypeOf(value).Kind() == reflect.Int32 {
		return true
	} else if reflect.TypeOf(value).Kind() == reflect.Int64 {
		return true
	} else if reflect.TypeOf(value).Kind() == reflect.Float32 {
		return true
	} else if reflect.TypeOf(value).Kind() == reflect.Float64 {
		return true
	} else if reflect.TypeOf(value).Kind() == reflect.Bool {
		return false
	} else if reflect.TypeOf(value).String() == "time.Time" {
		return true
	}

	return false
}

func IsCreditCardNumber(number string) bool {
	Re := regexp.MustCompile(`^(?:4[0-9]{12}(?:[0-9]{3})?|[25][1-7][0-9]{14}|6(?:011|5[0-9][0-9])[0-9]{12}|3[47][0-9]{13}|3(?:0[0-5]|[68][0-9])[0-9]{11}|(?:2131|1800|35\d{3})\d{11})$`)
	return Re.MatchString(number)
}

func IsPhoneNumber(number string) bool {
	Re := regexp.MustCompile(`^(?:(?:\(?(?:00|\+)([1-4]\d\d|[1-9]\d?)\)?)?[\-\.\ \\\/]?)?((?:\(?\d{1,}\)?[\-\.\ \\\/]?){0,})(?:[\-\.\ \\\/]?(?:#|ext\.?|extension|x)[\-\.\ \\\/]?(\d+))?$`)
	return Re.MatchString(number)
}

func IsEmail(email string) bool {
	Re := regexp.MustCompile("^[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+@[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)*$")

	return Re.MatchString(email)
}

func ToNumeric(value interface{}) float64 {
	var val float64
	if reflect.TypeOf(value).Kind() == reflect.String {
		val, _ = strconv.ParseFloat(value.(string), 64)
	} else if reflect.TypeOf(value).Kind() == reflect.Int {
		val = float64(value.(int))
	} else if reflect.TypeOf(value).Kind() == reflect.Int8 {
		val = float64(int(value.(int8)))
	} else if reflect.TypeOf(value).Kind() == reflect.Int16 {
		val = float64(int(value.(int16)))
	} else if reflect.TypeOf(value).Kind() == reflect.Int32 {
		val = float64(int(value.(int32)))
	} else if reflect.TypeOf(value).Kind() == reflect.Int64 {
		val = float64(int(value.(int64)))
	} else if reflect.TypeOf(value).Kind() == reflect.Float32 {
		val = float64(value.(float32))
	} else if reflect.TypeOf(value).Kind() == reflect.Float64 {
		val = value.(float64)
	} else if reflect.TypeOf(value).Kind() == reflect.Bool {
		if value.(bool) {
			val = 1.0
		} else {
			val = 0.0
		}
	} else if reflect.TypeOf(value).String() == "time.Time" {
		return float64(value.(time.Time).Unix()) // return the unix timestamp.
	} else {
		log.Panicln("Value with type:", reflect.TypeOf(value).String(), "cannot be convert to numerical value")
	}
	return val
}

func Round(x float64, n int) float64 {
	pow := math.Pow(10, float64(n))
	if math.Abs(x*pow) > 1e17 {
		return x
	}
	v, frac := math.Modf(x * pow)
	if x > 0.0 {
		if frac > 0.5 || (frac == 0.5 && uint64(v)%2 != 0) {
			v += 1.0
		}
	} else {
		if frac < -0.5 || (frac == -0.5 && uint64(v)%2 != 0) {
			v -= 1.0
		}
	}
	return v / pow
}

func Less(val0 interface{}, val1 interface{}) bool {
	if val0 == nil || val1 == nil {
		return true
	}

	if reflect.TypeOf(val0).Kind() == reflect.String {
		return val0.(string) < val1.(string)
	} else if reflect.TypeOf(val0).Kind() == reflect.Int {
		return val0.(int) < val1.(int)
	} else if reflect.TypeOf(val0).Kind() == reflect.Int8 {
		return val0.(int8) < val1.(int8)
	} else if reflect.TypeOf(val0).Kind() == reflect.Int16 {
		return val0.(int16) < val1.(int16)
	} else if reflect.TypeOf(val0).Kind() == reflect.Int32 {
		return val0.(int32) < val1.(int32)
	} else if reflect.TypeOf(val0).Kind() == reflect.Int64 {
		return val0.(int64) < val1.(int64)
	} else if reflect.TypeOf(val0).Kind() == reflect.Float32 {
		return val0.(float32) < val1.(float32)
	} else if reflect.TypeOf(val0).Kind() == reflect.Float64 {
		return val0.(float64) < val1.(float64)
	} else {
		log.Println("Value with type:", reflect.TypeOf(val0).String(), "cannot be compare!")
	}
	return false
}

/**
 * Get the mime type of a file.
 */
func GetFileContentType(out *os.File) (string, error) {

	// Only the first 512 bytes are used to sniff the content type.
	buffer := make([]byte, 512)

	_, err := out.Read(buffer)
	if err != nil {
		return "", err
	}

	// Use the net/http package's handy DectectContentType function. Always returns a valid
	// content-type by returning "application/octet-stream" if no others seemed to match.
	contentType := http.DetectContentType(buffer)

	return contentType, nil
}

/**
 * Keep the parent node
 */
func GetFilePathsByExtension(path string, extension string) []string {
	files, err := ioutil.ReadDir(path)
	results := make([]string, 0)
	if err == nil {
		for i := 0; i < len(files); i++ {
			if files[i].IsDir() {
				results = append(results, GetFilePathsByExtension(path+"/"+files[i].Name(), extension)...)
			} else if strings.HasSuffix(files[i].Name(), extension) {
				results = append(results, path+"/"+files[i].Name())
			}
		}
	}
	return results
}

// Copy the src file to dst. Any existing file will be overwritten and will not
// copy file attributes.
func Copy(src, dst string) error {
	in, err := os.Open(src)
	if err != nil {
		return err
	}
	defer in.Close()

	out, err := os.Create(dst)
	if err != nil {
		return err
	}
	defer out.Close()

	_, err = io.Copy(out, in)
	if err != nil {
		return err
	}
	return out.Close()
}

// Write a string to a given file.
func WriteStringToFile(filepath, s string) error {
	fo, err := os.Create(filepath)
	if err != nil {
		return err
	}
	defer fo.Close()

	_, err = io.Copy(fo, strings.NewReader(s))
	if err != nil {
		return err
	}

	return nil
}

func RemoveContents(dir string) error {
	d, err := os.Open(dir)
	if err != nil {
		return err
	}
	defer d.Close()
	names, err := d.Readdirnames(-1)
	if err != nil {
		return err
	}
	for _, name := range names {
		err = os.RemoveAll(filepath.Join(dir, name))
		if err != nil {
			return err
		}
	}
	return nil
}

func GetExecName(path string) string {
	var startIndex, endIndex int

	startIndex = strings.LastIndex(path, string(os.PathSeparator))
	if startIndex > -1 {
		path = path[startIndex+1:]
	}

	endIndex = strings.LastIndex(path, ".")

	if endIndex > -1 && startIndex > -1 {
		path = path[:endIndex]
	}

	return path
}

/** Open the browser at given url **/
func OpenBrowser(url string) {
	var err error

	switch runtime.GOOS {
	case "linux":
		err = exec.Command("xdg-open", url).Start()
	case "windows":
		err = exec.Command("rundll32", "url.dll,FileProtocolHandler", url).Start()
	case "darwin":
		err = exec.Command("open", url).Start()
	default:
		err = fmt.Errorf("unsupported platform")
	}
	if err != nil {
		log.Fatal(err)
	}

}

/**
 * Read output and send it to a channel.
 */
func ReadOutput(output chan string, rc io.ReadCloser) {

	cutset := "\r\n"
	for {
		buf := make([]byte, 3000)
		n, err := rc.Read(buf)
		if err != nil {
			if err != io.EOF {
				log.Println(err)
			}
			if n == 0 {
				break
			}
		}
		text := strings.TrimSpace(string(buf[:n]))
		for {
			// Take the index of any of the given cutset
			n := strings.IndexAny(text, cutset)
			if n == -1 {
				// If not found, but still have data, send it
				if len(text) > 0 {
					output <- text
				}
				break
			}
			// Send data up to the found cutset
			output <- text[:n]
			// If cutset is last element, stop there.
			if n == len(text) {
				break
			}
			// Shift the text and start again.
			text = text[n+1:]
		}
	}
}

func SvgToPng(input, output string, w, h int) error {

	in, err := os.Open(input)
	if err != nil {
		return err
	}
	defer in.Close()

	icon, _ := oksvg.ReadIconStream(in)
	icon.SetTarget(0, 0, float64(w), float64(h))
	rgba := image.NewRGBA(image.Rect(0, 0, w, h))
	icon.Draw(rasterx.NewDasher(w, h, rasterx.NewScannerGV(w, h, rgba, rgba.Bounds())), 1)

	out, err := os.Create(output)
	if err != nil {
		return err
	}
	defer out.Close()

	err = png.Encode(out, rgba)
	if err != nil {
		return err
	}

	return nil
}
