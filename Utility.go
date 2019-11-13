package Utility

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
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
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode"
	"unsafe"

	"github.com/glendc/go-external-ip"
	"github.com/kalafut/imohash"
	"github.com/pborman/uuid"
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

func Log(infos ...interface{}) {

	// if the channel is nil that's mean no processing function is running,
	// so I will create it once.
	if logFct == nil {
		logFct = func() {
			for {
				select {
				case msg := <-logChannel:
					log.Println(msg)
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
		return nil, errors.New("Out of Range Error")
	}
	return append(s[:index], s[index+1:]...), nil
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
	if _, err := os.Stat(name); err != nil {
		if os.IsNotExist(err) {
			return false
		}
	}
	return true
}

func CopyFile(source string, dest string) (err error) {
	sourcefile, err := os.Open(source)
	if err != nil {
		return err
	}

	defer sourcefile.Close()

	destfile, err := os.Create(dest)
	if err != nil {
		return err
	}

	defer destfile.Close()

	_, err = io.Copy(destfile, sourcefile)
	if err == nil {
		sourceinfo, err := os.Stat(source)
		if err != nil {
			err = os.Chmod(dest, sourceinfo.Mode())
		}

	}

	return
}

func CopyDir(source string, dest string) (err error) {

	// get properties of source dir
	sourceinfo, err := os.Stat(source)
	if err != nil {
		return err
	}

	// create dest dir

	err = os.MkdirAll(dest, sourceinfo.Mode())
	if err != nil {
		return err
	}

	directory, _ := os.Open(source)
	defer directory.Close()

	objects, err := directory.Readdir(-1)

	for _, obj := range objects {

		sourcefilepointer := source + "/" + obj.Name()

		destinationfilepointer := dest + "/" + obj.Name()

		if obj.IsDir() {
			// create sub-directories - recursively
			err = CopyDir(sourcefilepointer, destinationfilepointer)
			if err != nil {
				fmt.Println(err)
			}
		} else {
			// perform copy
			err = CopyFile(sourcefilepointer, destinationfilepointer)
			if err != nil {
				fmt.Println(err)
			}
		}
	}
	return
}

/**
 * Copy the content of a directory to another directory.
 */
func CopyDirContent(source string, dest string) (err error) {

	fileInfo, err := ioutil.ReadDir(source)
	if err != nil {
		log.Println("-------> ", err)
		return err
	}

	// copy file and directory...
	for _, file := range fileInfo {
		if file.IsDir() {
			log.Println("---> copy dir ", source+string(os.PathSeparator)+file.Name(), "to", dest+string(os.PathSeparator)+file.Name())
			CopyDir(source+string(os.PathSeparator)+file.Name(), dest+string(os.PathSeparator)+file.Name())
		} else {
			log.Println("---> copy file ", source+string(os.PathSeparator)+file.Name(), "to", dest+string(os.PathSeparator)+file.Name())
			CopyFile(source+string(os.PathSeparator)+file.Name(), dest+string(os.PathSeparator)+file.Name())
		}
	}
	return nil
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

func CompressDir(src string, buf io.Writer) error {
	// tar > gzip > buf
	zr := gzip.NewWriter(buf)
	tw := tar.NewWriter(zr)

	// walk through every file in the folder
	filepath.Walk(src, func(file string, fi os.FileInfo, err error) error {
		// generate tar header
		header, err := tar.FileInfoHeader(fi, file)
		if err != nil {
			return err
		}

		// must provide real name
		// (see https://golang.org/src/archive/tar/common.go?#L626)
		header.Name = filepath.ToSlash(file)

		// write header
		if err := tw.WriteHeader(header); err != nil {
			return err
		}
		// if not a dir, write file content
		if !fi.IsDir() {
			data, err := os.Open(file)
			defer data.Close()

			if err != nil {
				return err
			}
			if _, err := io.Copy(tw, data); err != nil {
				return err
			}

		}
		return nil
	})

	// produce tar
	if err := tw.Close(); err != nil {
		return err
	}
	// produce gzip
	if err := zr.Close(); err != nil {
		return err
	}
	//
	return nil
}

func ExtractTarGz(gzipStream io.Reader) {
	uncompressedStream, err := gzip.NewReader(gzipStream)
	if err != nil {
		log.Fatal("ExtractTarGz: NewReader failed")
	}

	tarReader := tar.NewReader(uncompressedStream)

	for true {
		header, err := tarReader.Next()

		if err == io.EOF {
			break
		}

		if err != nil {
			log.Fatalf("ExtractTarGz: Next() failed: %s", err.Error())
		}

		switch header.Typeflag {
		case tar.TypeDir:
			if err := os.Mkdir(header.Name, 0755); err != nil {
				log.Fatalf("ExtractTarGz: Mkdir() failed: %s", err.Error())
			}
		case tar.TypeReg:
			outFile, err := os.Create(header.Name)
			if err != nil {
				log.Fatalf("ExtractTarGz: Create() failed: %s", err.Error())
			}
			if _, err := io.Copy(outFile, tarReader); err != nil {
				log.Fatalf("ExtractTarGz: Copy() failed: %s", err.Error())
			}
			outFile.Close()

		default:
			log.Fatalf(
				"ExtractTarGz: uknown type: %s in %s",
				header.Typeflag,
				header.Name)
		}
	}
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
	str, _ := ToJson(map[string]string{"FunctionName": functionName, "FileLine": fileLine, "ErrorMsg": err.Error()})
	return str
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

func validIP4(ipAddress string) bool {
	ipAddress = strings.Trim(ipAddress, " ")

	re, _ := regexp.Compile(`^(([0-9]|[1-9][0-9]|1[0-9]{2}|2[0-4][0-9]|25[0-5])\.){3}([0-9]|[1-9][0-9]|1[0-9]{2}|2[0-4][0-9]|25[0-5])$`)
	if re.MatchString(ipAddress) {
		return true
	}
	return false
}

func MyIP() string {

	consensus := externalip.DefaultConsensus(nil, nil)
	// Get your IP,
	// which is never <nil> when err is <nil>.
	ip, err := consensus.ExternalIP()
	if err == nil {
		return ip.String() // print IPv4/IPv6 in string format
	}
	return ""
}

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
				return ipnet.IP.String()
			}
		}
	}
	return ""
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
	} else {
		log.Panicln("Value with type:", reflect.TypeOf(value).String(), "cannot be convert to string")
	}
	// Remove leading space.
	return strings.TrimSpace(str)
}

func ToInt(value interface{}) int {
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
