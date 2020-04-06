#!/usr/bin/python3

"""
* Copyright (c) 2009, Jeffrey Tchang
* Additional *pike
* Ported to python 3 by hilbert70
* Added commandline stuff (argparse)
* Geotagging will probably not work, I had no way to test that
* Added debugging flag
* Changed the demaon stuff, stop did not wrok, is working now
*
* All rights reserved.
*
*
* THIS SOFTWARE IS PROVIDED ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
"""

import sys
import os
import io
import tempfile
import psutil
import errno
import atexit
import logging
import logging.handlers
import configparser
import signal
from signal import SIGTERM
import time
import argparse 
import traceback

import socketserver
# use http.server instead of BaseHTTPServer
#from http.server  import BaseHTTPRequestHandler, HTTPServer
import http.server
import xml.sax
from xml.sax.handler import ContentHandler
import xml.dom.minidom

import hashlib
import binascii
import select
import tarfile
import random
import cgi
import datetime

parser = argparse.ArgumentParser(description="This server will be up and Eye-Fi cards can connect to it.\n GeoTaggnig is proably not working, I could not test this.\nA full path to the configuriation path must be given.")
argGroup = parser.add_mutually_exclusive_group(required=True)
argGroup.add_argument("action",metavar="start",  help="Start the server", nargs="?", action="append" )
argGroup.add_argument("action",metavar="stop",   help="Stop the server", nargs="?", action="append")
argGroup.add_argument("action",metavar="restart",help="Restart the server",  nargs="?", action="append")
argGroup.add_argument("action",metavar="reload", help="Reload the configuration", nargs="?", action="append")
argGroup.add_argument("action",metavar="status", help="Show the status of the server", nargs="?", action="append")
argGroup.add_argument("action",metavar="instance",  nargs="?", action="append")
parser.add_argument("-c", "--configure", required=True, nargs=1)
parser.add_argument("-l", "--logfile", required=True,nargs=1)
parser.add_argument("-d", "--debug", default=0, type=int, help="Set debug level: \
CRITICAL = 50, \
ERROR = 40, \
WARNING = 30, \
INFO = 20, \
DEBUG=10, \
NOTSET=0")
args = parser.parse_args()

#print("Action file: " + args.action[0]) 
#print("Config file: " + args.configure[0]) 
#print("Logfile file: " + args.logfile[0]) 
# Create the main logger
eyeFiLogger = logging.Logger("eyeFiLogger",args.debug)

# Create two handlers. One to print to the log and one to print to the console
consoleHandler = logging.StreamHandler(sys.stdout)

# Set how both handlers will print the pretty log events
eyeFiLoggingFormat = logging.Formatter("[%(asctime)s][%(funcName)s] - %(message)s",'%m/%d/%y %I:%M%p')
consoleHandler.setFormatter(eyeFiLoggingFormat)

# Append both handlers to the main Eye Fi Server logger
eyeFiLogger.addHandler(consoleHandler)

class Daemon(object):
    """
    Usage: - create your own a subclass Daemon class and override the run() method. Run() will be periodically the calling inside the infinite run loop
           - you can receive reload signal from self.isReloadSignal and then you have to set back self.isReloadSignal = False
    """

    def __init__(self, stdin='/dev/null', stdout='/dev/null', stderr='/dev/null'):
        self.ver = 0.1  # version
        self.pauseRunLoop = 0    # 0 means none pause between the calling of run() method.
        self.restartPause = 1    # 0 means without a pause between stop and start during the restart of the daemon
        self.waitToHardKill = 3  # when terminate a process, wait until kill the process with SIGTERM signal

        self.isReloadSignal = False
        self._canDaemonRun = True
        self.processName = sys.argv[0] #os.path.basename(sys.argv[0])
        self.stdin = stdin
        self.stdout = stdout
        self.stderr = stderr

    def _sigterm_handler(self, signum, frame):
        self._canDaemonRun = False

    def _reload_handler(self, signum, frame):
        self.isReloadSignal = True

    def _makeDaemon(self):
        """
        Make a daemon, do double-fork magic.
        """

        try:
            pid = os.fork()
            if pid > 0:
                # Exit first parent.
                sys.exit(0)
        except OSError as e:
            m = f"Fork #1 failed: {e}"
            print(m)
            sys.exit(1)

        # Decouple from the parent environment.
        os.chdir("/")
        os.setsid()
        os.umask(0)

        # Do second fork.
        try:
            pid = os.fork()
            if pid > 0:
                # Exit from second parent.
                sys.exit(0)
        except OSError as e:
            m = f"Fork #2 failed: {e}"
            print(m)
            sys.exit(1)

        m = "The daemon process is going to background."
        print(m)

        # Redirect standard file descriptors.
        sys.stdout.flush()
        sys.stderr.flush()
        si = open(self.stdin, 'r')
        so = open(self.stdout, 'a+')
        se = open(self.stderr, 'a+')
        os.dup2(si.fileno(), sys.stdin.fileno())
        os.dup2(so.fileno(), sys.stdout.fileno())
        os.dup2(se.fileno(), sys.stderr.fileno())

    def _getProces(self):
        procs = []

        for p in psutil.process_iter():
            if self.processName in p.cmdline(): #[part.split('/')[-1] for part in p.cmdline()]:
                # Skip  the current process
                if p.pid != os.getpid():
                    procs.append(p)
 
        return procs

    def start(self):
        """
        Start daemon.
        """

        # Handle signals
        signal.signal(signal.SIGINT, self._sigterm_handler)
        signal.signal(signal.SIGTERM, self._sigterm_handler)
        signal.signal(signal.SIGHUP, self._reload_handler)

        # Check if the daemon is already running.
        procs = self._getProces()

        if procs:
            pids = ",".join([str(p.pid) for p in procs])
            m = f"Find a previous daemon processes with PIDs {pids}. Is not already the daemon running?"
            print(m)
            sys.exit(1)
        else:
            m = f"Start the daemon version {self.ver}"
            print(m)

        # Daemonize the main process
        self._makeDaemon()
        # Start a infinitive loop that periodically runs run() method
        self._infiniteLoop()

    def version(self):
        m = f"The daemon version {self.ver}"
        print(m)

    def status(self):
        """
        Get status of the daemon.
        """

        procs = self._getProces()

        if procs:
            pids = ",".join([str(p.pid) for p in procs])
            m = f"The daemon is running with PID {pids}."
            print(m)
        else:
            m = "The daemon is not running!"
            print(m)

    def reload(self):
        """
        Reload the daemon.
        """

        procs = self._getProces()

        if procs:
            for p in procs:
                os.kill(p.pid, signal.SIGHUP)
                m = f"Send SIGHUP signal into the daemon process with PID {p.pid}."
                print(m)
        else:
            m = "The daemon is not running!"
            print(m)

    def stop(self):
        """
        Stop the daemon.
        """

        procs = self._getProces()

        def on_terminate(process):
            m = f"The daemon process with PID {process.pid} has ended correctly."
            print(m)

        if procs:
            for p in procs:
                p.terminate()

            gone, alive = psutil.wait_procs(procs, timeout=self.waitToHardKill, callback=on_terminate)

            for p in alive:
                m = f"The daemon process with PID {p.pid} was killed with SIGTERM!"
                print(m)
                p.kill()
        else:
            m = "Cannot find some daemon process, I will do nothing."
            print(m)

    def restart(self):
        """
        Restart the daemon.
        """
        self.stop()

        if self.restartPause:
            time.sleep(self.restartPause)

        self.start()

    def _infiniteLoop(self):
        try:
            if self.pauseRunLoop:
                time.sleep(self.pauseRunLoop)

                while self._canDaemonRun:
                    self.run()
                    time.sleep(self.pauseRunLoop)
            else:
                while self._canDaemonRun:
                    self.run()

        except Exception as e:
            m = f"Run method failed: {e}"
            sys.stderr.write(m)
            sys.exit(1)

    # this method you have to override
    def run(self):
        pass

def fix_ownership(path, uid, gid):
   if uid != -1 and gid != -1:
       os.chown(path, uid, gid)


# Implements an EyeFi server
class EyeFiServer(socketserver.ThreadingMixIn, http.server.HTTPServer):

    def serve_forever(self):
        while self.run:
            try:
                self.handle_request()
            except select.error( e ):
                if e[0] != errno.EINTR:
                    raise e

    def reload_config(self, signum, frame):
        try:
            configfile = args.configure[0]
            eyeFiLogger.info("Reloading configuration " + configfile)
            self.config.read(configfile)
        except:
            eyeFiLogger.error("Error reloading configuration")

    def stop_server(self, signum, frame):
        try:
            eyeFiLogger.info("Eye-Fi server stopped ")
            self.stop()
        except:
            eyeFiLogger.error("Error stopping server")

    def server_bind(self):

        http.server.HTTPServer.server_bind(self)
        self.socket.settimeout(None)
        signal.signal(signal.SIGUSR1, self.reload_config)
        signal.signal(signal.SIGTERM, self.stop_server)
        signal.signal(signal.SIGINT, self.stop_server)
        self.run = True

    def get_request(self):
        while self.run:
            try:
                connection, address = self.socket.accept()
                eyeFiLogger.debug("Incoming connection from client %s" % address[0])

                connection.settimeout(None)
                return (connection, address)

            except socket.timeout:
                self.socket.close()
                pass

    def stop(self):
        self.run = False

    # alt serve_forever method for python <2.6
    # because we want a shutdown mech ..
    #def serve(self):
    #  while self.run:
    #    self.handle_request()
    #  self.socket.close()

# This class is responsible for handling HTTP requests passed to it.
# It implements the two most common HTTP methods, do_GET() and do_POST()

# Eye Fi XML SAX ContentHandler
class EyeFiContentHandler(ContentHandler):

    # These are the element names that I want to parse out of the XML
    elementNamesToExtract = ["macaddress","cnonce","transfermode","transfermodetimestamp","fileid","filename","filesize","filesignature"]

    # For each of the element names I create a dictionary with the value to False
    elementsToExtract = {}

    # Where to put the extracted values
    extractedElements = {}


    def __init__(self):

        self.extractedElements = {}

        for elementName in self.elementNamesToExtract:
            self.elementsToExtract[elementName] = False

    def startElement(self, name, attributes):

        # If the name of the element is a key in the dictionary elementsToExtract
        # set the value to True
        if name in self.elementsToExtract:
            self.elementsToExtract[name] = True

    def endElement(self, name):

        # If the name of the element is a key in the dictionary elementsToExtract
        # set the value to False
        if name in self.elementsToExtract:
            self.elementsToExtract[name] = False


    def characters(self, content):

        for elementName in self.elementsToExtract:
            if self.elementsToExtract[elementName] == True:
                self.extractedElements[elementName] = content



class EyeFiRequestHandler(http.server.BaseHTTPRequestHandler):

    # pike: these seem unused ?
    protocol_version = 'HTTP/1.1'
    sys_version = ""
    server_version = "Eye-Fi Agent/2.0.4.0 (Windows XP SP2)"

    def do_QUIT (self):
        eyeFiLogger.debug("Got StopServer request .. stopping server")
        self.send_response(200)
        self.end_headers()
        self.server.stop()

    def do_GET(self):
        try:
            eyeFiLogger.debug(self.command + " " + self.path + " " + self.request_version)

            SOAPAction = ""
            eyeFiLogger.debug("Headers received in GET request:")
            for headerName,headerValue in self.headers.items():
                if( headerName == "SOAPAction"):
                    SOAPAction = headerValue

            self.send_response(200)
            self.send_header('Content-type','text/html')
            # I should be sending a Content-Length header with HTTP/1.1 but I am being lazy
            # self.send_header('Content-length', '123')
            self.end_headers()
            self.wfile.write(self.client_address)
            self.wfile.write(self.headers)
            self.close_connection = 0
        except:
            eyeFiLogger.error("Got an an exception:")
            eyeFiLogger.error(traceback.format_exc())
            raise


    def do_POST(self):
        try:
            eyeFiLogger.debug(self.command + " " + self.path + " " + self.request_version)

            SOAPAction = ""
            contentLength = ""

            # Loop through all the request headers and pick out ones that are relevant
            contentLength=0
            eyeFiLogger.debug("Headers received in POST request:")
            for headerName,headerValue in self.headers.items():
                if( headerName == "SOAPAction"):
                    SOAPAction = headerValue

                if( headerName == "Content-Length"):
                    contentLength = int(headerValue)

                eyeFiLogger.debug("Header: " +headerName + ": " + headerValue)


            # Read contentLength byte s worth of data
            eyeFiLogger.debug("Attempting to read " + str(contentLength) + " bytes of data")
            # postData = self.rfile.read(contentLength)
            chunksize = 1048576 # 1MB

            mem = io.BytesIO()
            while True:
                remain = contentLength - int(mem.tell())
                if remain <= 0: break
                chunk = self.rfile.read(min(chunksize, remain))
                if not len(chunk): break
                mem.write(chunk)
                print( remain )
            postData = mem.getvalue()
            mem.close()

            eyeFiLogger.debug("Finished reading " + str(contentLength) + " bytes of data")

            # Perform action based on path and SOAPAction
            # A SOAPAction of StartSession indicates the beginning of an EyeFi
            # authentication request
            if((self.path == "/api/soap/eyefilm/v1") and (SOAPAction == "\"urn:StartSession\"")):
                eyeFiLogger.debug("Got StartSession request")
                response = self.startSession(postData)
                contentLength = len(response)

                eyeFiLogger.debug("StartSession response: " + str(response))

                self.send_response(200)
                self.send_header('Date', self.date_time_string())
                self.send_header('Pragma','no-cache')
                self.send_header('Server','Eye-Fi Agent/2.0.4.0 (Windows XP SP2)')
                self.send_header('Content-Type','text/xml; charset="utf-8"')
                self.send_header('Content-Length', contentLength)
                self.end_headers()

                self.wfile.write(response)
                self.wfile.flush()
                self.handle_one_request()

            # GetPhotoStatus allows the card to query if a photo has been uploaded
            # to the server yet
            if((self.path == "/api/soap/eyefilm/v1") and (SOAPAction == "\"urn:GetPhotoStatus\"")):
                eyeFiLogger.debug("Got GetPhotoStatus request")

                response = self.getPhotoStatus(postData)
                contentLength = len(response)

                eyeFiLogger.debug("GetPhotoStatus response: " + str(response))

                self.send_response(200)
                self.send_header('Date', self.date_time_string())
                self.send_header('Pragma','no-cache')
                self.send_header('Server','Eye-Fi Agent/2.0.4.0 (Windows XP SP2)')
                self.send_header('Content-Type','text/xml; charset="utf-8"')
                self.send_header('Content-Length', contentLength)
                self.end_headers()

                self.wfile.write(response)
                self.wfile.flush()


            # If the URL is upload and there is no SOAPAction the card is ready to send a picture to me
            if((self.path == "/api/soap/eyefilm/v1/upload") and (SOAPAction == "")):
                eyeFiLogger.debug("Got upload request")
                response = self.uploadPhoto(postData)
                contentLength = len(response)

                eyeFiLogger.debug("Upload response: " + str(response))

                self.send_response(200)
                self.send_header('Date', self.date_time_string())
                self.send_header('Pragma','no-cache')
                self.send_header('Server','Eye-Fi Agent/2.0.4.0 (Windows XP SP2)')
                self.send_header('Content-Type','text/xml; charset="utf-8"')
                self.send_header('Content-Length', contentLength)
                self.end_headers()

                self.wfile.write(response)
                self.wfile.flush()

            # If the URL is upload and SOAPAction is MarkLastPhotoInRoll
            if((self.path == "/api/soap/eyefilm/v1") and (SOAPAction == "\"urn:MarkLastPhotoInRoll\"")):
                eyeFiLogger.debug("Got MarkLastPhotoInRoll request")
                response = self.markLastPhotoInRoll(postData)
                contentLength = len(response)

                eyeFiLogger.debug("MarkLastPhotoInRoll response: " + str(response))
                self.send_response(200)
                self.send_header('Date', self.date_time_string())
                self.send_header('Pragma','no-cache')
                self.send_header('Server','Eye-Fi Agent/2.0.4.0 (Windows XP SP2)')
                self.send_header('Content-Type','text/xml; charset="utf-8"')
                self.send_header('Content-Length', contentLength)
                self.send_header('Connection', 'Close')
                self.end_headers()

                self.wfile.write(response)
                self.wfile.flush()

                eyeFiLogger.debug("Connection closed.")
        except:
            eyeFiLogger.error("Got an an exception:")
            eyeFiLogger.error(traceback.format_exc())
            raise


    # Handles MarkLastPhotoInRoll action
    def markLastPhotoInRoll(self,postData):
        # Create the XML document to send back
        doc = xml.dom.minidom.Document()

        SOAPElement = doc.createElementNS("http://schemas.xmlsoap.org/soap/envelope/","SOAP-ENV:Envelope")
        SOAPElement.setAttribute("xmlns:SOAP-ENV","http://schemas.xmlsoap.org/soap/envelope/")
        SOAPBodyElement = doc.createElement("SOAP-ENV:Body")

        markLastPhotoInRollResponseElement = doc.createElement("MarkLastPhotoInRollResponse")

        SOAPBodyElement.appendChild(markLastPhotoInRollResponseElement)
        SOAPElement.appendChild(SOAPBodyElement)
        doc.appendChild(SOAPElement)

        return doc.toxml(encoding="UTF-8")


    # Handles receiving the actual photograph from the card.
    # postData will most likely contain multipart binary post data that needs to be parsed
    def uploadPhoto(self,postData):

        # Take the postData string and work with it as if it were a file object
        postDataInMemoryFile = io.BytesIO(postData)

        # Get the content-type header which looks something like this
        # content-type: multipart/form-data; boundary=---------------------------02468ace13579bdfcafebabef00d
        contentTypeHeader = self.headers['Content-Type']
        eyeFiLogger.debug(contentTypeHeader)

        # Extract the boundary parameter in the content-type header
        headerParameters = contentTypeHeader.split(";")
        eyeFiLogger.debug(headerParameters)

        boundary = headerParameters[-1].split("=")
        boundary = boundary[1].strip()
        eyeFiLogger.debug("Extracted boundary: " + boundary)

        # eyeFiLogger.debug("uploadPhoto postData: " + postData)

        # Parse the multipart/form-data
        form = cgi.parse_multipart(postDataInMemoryFile, {"boundary":boundary.encode(),"content-disposition":self.headers['content-disposition']})
        eyeFiLogger.debug("Available multipart/form-data: " + str(form.keys()))

        # Parse the SOAPENVELOPE using the EyeFiContentHandler()
        soapEnvelope = form['SOAPENVELOPE'][0].decode()
        eyeFiLogger.debug("SOAPENVELOPE: " + soapEnvelope)
        handler = EyeFiContentHandler()
        parser = xml.sax.parseString(soapEnvelope,handler)

        eyeFiLogger.debug("Extracted elements: " + str(handler.extractedElements))


        imageTarfileName = handler.extractedElements["filename"]

        #pike
        uid = self.server.config.getint('EyeFiServer','upload_uid')
        gid = self.server.config.getint('EyeFiServer','upload_gid')
        file_mode = self.server.config.get('EyeFiServer','upload_file_mode')
        dir_mode = self.server.config.get('EyeFiServer','upload_dir_mode')
        eyeFiLogger.debug("Using uid/gid %d/%d"%(uid,gid))
        eyeFiLogger.debug("Using file_mode " + file_mode)
        eyeFiLogger.debug("Using dir_mode " + dir_mode)

        geotag_enable = int(self.server.config.getint('EyeFiServer','geotag_enable'))
        if geotag_enable:
            geotag_accuracy = int(self.server.config.get('EyeFiServer','geotag_accuracy'))

        imageTarPath = os.path.join(tempfile.gettempdir(), imageTarfileName)
        eyeFiLogger.debug("Generated path " + imageTarPath)

        fileHandle = open(imageTarPath, 'wb')
        eyeFiLogger.debug("Opened file " + imageTarPath + " for binary writing")

        fileHandle.write(form['FILENAME'][0])
        eyeFiLogger.debug("Wrote file " + imageTarPath)

        fileHandle.close()
        eyeFiLogger.debug("Closed file " + imageTarPath)

        eyeFiLogger.debug("Extracting TAR file " + imageTarPath)
        try:
            imageTarfile = tarfile.open(imageTarPath)
        except ReadError( error ):
            eyeFiLogger.error("Failed to open %s" % imageTarPath)
            raise

        for member in imageTarfile.getmembers():
            # If timezone is a daylight savings timezone, and we are
            # currently in daylight savings time, then use the altzone
            if time.daylight != 0 and time.localtime().tm_isdst != 0:
                timeoffset = time.altzone
            else:
                timeoffset = time.timezone
            timezone = timeoffset / 60 / 60 * -1
            imageDate = datetime.datetime.fromtimestamp(member.mtime) - datetime.timedelta(hours=timezone)
            uploadDir = imageDate.strftime(self.server.config.get('EyeFiServer','upload_dir'))
            eyeFiLogger.debug("Creating folder " + uploadDir)
            if not os.path.isdir(uploadDir):
                os.makedirs(uploadDir)
                fix_ownership(uploadDir, uid, gid)
                if file_mode != "":
                    os.chmod(uploadDir, int(dir_mode))

            f=imageTarfile.extract(member, uploadDir)
            imagePath = os.path.join(uploadDir, member.name)
            eyeFiLogger.debug("imagePath " + imagePath)
            os.utime(imagePath, (member.mtime + timeoffset, member.mtime + timeoffset))
            fix_ownership(imagePath, uid, gid)
            if file_mode != "":
                os.chmod(imagePath, int(file_mode))

            if geotag_enable>0 and member.name.lower().endswith(".log"):
                eyeFiLogger.debug("Processing LOG file " + imagePath)
                try:
                    imageName = member.name[:-4]
                    shottime, aps = list(self.parselog(imagePath,imageName))
                    aps = self.getphotoaps(shottime, aps)
                    loc = self.getlocation(aps)
                    if loc['status']=='OK' and float(loc['accuracy'])<=geotag_accuracy:
                        xmpName=imageName+".xmp"
                        xmpPath=os.path.join(uploadDir, xmpName)
                        eyeFiLogger.debug("Writing XMP file " + xmpPath)
                        self.writexmp(xmpPath,float(loc['location']['lat']),float(loc['location']['lng']))
                        fix_ownership(xmpPath, uid, gid)
                        if file_mode != "":
                            os.chmod(xmpPath, int(file_mode))
                except:
                    eyeFiLogger.error("Error processing LOG file " + imagePath)

        eyeFiLogger.debug("Closing TAR file " + imageTarPath)
        imageTarfile.close()

        eyeFiLogger.debug("Deleting TAR file " + imageTarPath)
        os.remove(imageTarPath)

        # Create the XML document to send back
        doc = xml.dom.minidom.Document()

        SOAPElement = doc.createElementNS("http://schemas.xmlsoap.org/soap/envelope/","SOAP-ENV:Envelope")
        SOAPElement.setAttribute("xmlns:SOAP-ENV","http://schemas.xmlsoap.org/soap/envelope/")
        SOAPBodyElement = doc.createElement("SOAP-ENV:Body")

        uploadPhotoResponseElement = doc.createElement("UploadPhotoResponse")
        successElement = doc.createElement("success")
        successElementText = doc.createTextNode("true")

        successElement.appendChild(successElementText)
        uploadPhotoResponseElement.appendChild(successElement)

        SOAPBodyElement.appendChild(uploadPhotoResponseElement)
        SOAPElement.appendChild(SOAPBodyElement)
        doc.appendChild(SOAPElement)

        return doc.toxml(encoding="UTF-8")

    def parselog(self,logfile,filename):
        shottime = 0
        aps = {}
        for line in open(logfile):
            time, timestamp, act = line.strip().split(",", 2)
            act = act.split(",")
            act, args = act[0], act[1:]
            if act in ("AP", "NEWAP"):
                aps.setdefault(args[0], []).append({"time": int(time),"pwr": int(args[1])})
            elif act == "NEWPHOTO":
                if filename==args[0]:
                    shottime = int(time)
            elif act == "POWERON":
                if shottime>0:
                    return shottime, aps
                shottime = 0
                aps = {}
        if shottime>0:
            return shottime, aps

    def getphotoaps(self, time, aps):
        geotag_lag = int(self.server.config.get('EyeFiServer','geotag_lag'))
        newaps = []
        for mac in aps:
            lag = min([(abs(ap["time"] - time), ap["pwr"]) for ap in aps[mac]], key=lambda a: a[0])
            if lag[0] <= geotag_lag:
                newaps.append({"mac": mac, "pwr": lag[1]})
        return newaps

    def getlocation(self, aps):
        try:
            geourl = 'maps.googleapis.com'
            headers = {"Host": geourl}
            params = "?browser=none&sensor=false"
            for ap in aps:
                params+='&wifi=mac:'+'-'.join([ap['mac'][2*d:2*d+2] for d in range(6)])+'|ss:'+str(int(math.log10(ap['pwr']/100.0)*10-50))
            conn = httplib.HTTPSConnection(geourl)
            conn.request("GET", "/maps/api/browserlocation/json"+params, "", headers)
            resp = conn.getresponse()
            result = resp.read()
            conn.close()
        except:
            eyeFiLogger.debug("Error connecting to geolocation service")
            return None
        try:
            try:
                import simplejson as json
            except ImportError:
                import json
            return json.loads(result)
        except:
            try:
                import re
                result=result.replace("\n"," ")
                loc={}
                loc['location']={}
                loc['location']['lat']=float(re.sub(r'.*"lat"\s*:\s*([\d.]+)\s*[,}\n]+.*',r'\1',result))
                loc['location']['lng']=float(re.sub(r'.*"lng"\s*:\s*([\d.]+)\s*[,}\n]+.*',r'\1',result))
                loc['accuracy']=float(re.sub(r'.*"accuracy"\s*:\s*([\d.]+)\s*[,\}\n]+.*',r'\1',result))
                loc['status']=re.sub(r'.*"status"\s*:\s*"(.*?)"\s*[,}\n]+.*',r'\1',result)
                return loc
            except:
                eyeFiLogger.debug("Geolocation service response contains no coordinates: " + result)
                return None

    def writexmp(self,name,latitude,longitude):
        if latitude>0:
            ref="N"
        else:
            ref="S"
        latitude=str(abs(latitude)).split('.')
        latitude[1]=str(float('0.'+latitude[1])*60)
        latitude=','.join(latitude)+ref

        if longitude>0:
            ref="E"
        else:
            ref="W"
        longitude=str(abs(longitude)).split('.')
        longitude[1]=str(float('0.'+longitude[1])*60)
        longitude=','.join(longitude)+ref

        FILE = open(name,"w")
        FILE.write("<?xpacket begin='\xef\xbb\xbf' id='W5M0MpCehiHzreSzNTczkc9d'?>\n<x:xmpmeta xmlns:x='adobe:ns:meta/' x:xmptk='EyeFiServer'>\n<rdf:RDF xmlns:rdf='http://www.w3.org/1999/02/22-rdf-syntax-ns#'>\n<rdf:Description rdf:about='' xmlns:exif='http://ns.adobe.com/exif/1.0/'>\n<exif:GPSLatitude>"+latitude+"</exif:GPSLatitude>\n<exif:GPSLongitude>"+longitude+"</exif:GPSLongitude>\n<exif:GPSVersionID>2.2.0.0</exif:GPSVersionID>\n</rdf:Description>\n</rdf:RDF>\n</x:xmpmeta>\n<?xpacket end='w'?>\n")
        FILE.close()

    def getPhotoStatus(self,postData):
        handler = EyeFiContentHandler()
        parser = xml.sax.parseString(postData,handler)

        # Create the XML document to send back
        doc = xml.dom.minidom.Document()

        SOAPElement = doc.createElementNS("http://schemas.xmlsoap.org/soap/envelope/","SOAP-ENV:Envelope")
        SOAPElement.setAttribute("xmlns:SOAP-ENV","http://schemas.xmlsoap.org/soap/envelope/")
        SOAPBodyElement = doc.createElement("SOAP-ENV:Body")

        getPhotoStatusResponseElement = doc.createElement("GetPhotoStatusResponse")
        getPhotoStatusResponseElement.setAttribute("xmlns","http://localhost/api/soap/eyefilm")

        fileidElement = doc.createElement("fileid")
        fileidElementText = doc.createTextNode("1")
        fileidElement.appendChild(fileidElementText)

        offsetElement = doc.createElement("offset")
        offsetElementText = doc.createTextNode("0")
        offsetElement.appendChild(offsetElementText)

        getPhotoStatusResponseElement.appendChild(fileidElement)
        getPhotoStatusResponseElement.appendChild(offsetElement)

        SOAPBodyElement.appendChild(getPhotoStatusResponseElement)

        SOAPElement.appendChild(SOAPBodyElement)
        doc.appendChild(SOAPElement)

        return doc.toxml(encoding="UTF-8")

    def _get_mac_uploadkey_dict(self):
        macs = {}
        upload_keys = {}
        for key, value in self.server.config.items('EyeFiServer'):
            if key.find('upload_key_') == 0:
                index = int(key[11:])
                upload_keys[index] = value
            elif key.find('mac_') == 0:
                index = int(key[4:])
                macs[index] = value
        d = {}
        for key in macs.keys():
            d[macs[key]] = upload_keys[key]
        return d

    def startSession(self, postData):
        eyeFiLogger.debug("Delegating the XML parsing of startSession postData to EyeFiContentHandler()")
        handler = EyeFiContentHandler()
        parser = xml.sax.parseString(postData,handler)

        eyeFiLogger.debug("Extracted elements: " + str(handler.extractedElements))

        # Retrieve it from C:\Documents and Settings\<User>\Application Data\Eye-Fi\Settings.xml
        mac_to_uploadkey_map = self._get_mac_uploadkey_dict()
        mac = handler.extractedElements["macaddress"]
        upload_key = mac_to_uploadkey_map[mac]
        eyeFiLogger.debug("Got MAC address of " + mac)
        eyeFiLogger.debug("Setting Eye-Fi upload key to " + upload_key)

        credentialString = mac + handler.extractedElements["cnonce"] + upload_key
        eyeFiLogger.debug("Concatenated credential string (pre MD5): " + credentialString)

        # Return the binary data represented by the hexadecimal string
        # resulting in something that looks like "\x00\x18V\x03\x04..."
        binaryCredentialString = binascii.unhexlify(credentialString)

        # Now MD5 hash the binary string
        m = hashlib.md5()
        m.update(binaryCredentialString)

        # Hex encode the hash to obtain the final credential string
        credential = m.hexdigest()

        # Create the XML document to send back
        doc = xml.dom.minidom.Document()

        SOAPElement = doc.createElementNS("http://schemas.xmlsoap.org/soap/envelope/","SOAP-ENV:Envelope")
        SOAPElement.setAttribute("xmlns:SOAP-ENV","http://schemas.xmlsoap.org/soap/envelope/")
        SOAPBodyElement = doc.createElement("SOAP-ENV:Body")


        startSessionResponseElement = doc.createElement("StartSessionResponse")
        startSessionResponseElement.setAttribute("xmlns","http://localhost/api/soap/eyefilm")

        credentialElement = doc.createElement("credential")
        credentialElementText = doc.createTextNode(credential)
        credentialElement.appendChild(credentialElementText)

        snonceElement = doc.createElement("snonce")
        snonceElementText = doc.createTextNode("%x" % random.getrandbits(128))
        snonceElement.appendChild(snonceElementText)

        transfermodeElement = doc.createElement("transfermode")
        transfermodeElementText = doc.createTextNode(handler.extractedElements["transfermode"])
        transfermodeElement.appendChild(transfermodeElementText)

        transfermodetimestampElement = doc.createElement("transfermodetimestamp")
        transfermodetimestampElementText = doc.createTextNode(handler.extractedElements["transfermodetimestamp"])
        transfermodetimestampElement.appendChild(transfermodetimestampElementText)

        upsyncallowedElement = doc.createElement("upsyncallowed")
        upsyncallowedElementText = doc.createTextNode("true")
        upsyncallowedElement.appendChild(upsyncallowedElementText)

        startSessionResponseElement.appendChild(credentialElement)
        startSessionResponseElement.appendChild(snonceElement)
        startSessionResponseElement.appendChild(transfermodeElement)
        startSessionResponseElement.appendChild(transfermodetimestampElement)
        startSessionResponseElement.appendChild(upsyncallowedElement)

        SOAPBodyElement.appendChild(startSessionResponseElement)

        SOAPElement.appendChild(SOAPBodyElement)
        doc.appendChild(SOAPElement)


        return doc.toxml(encoding="UTF-8")


eyeFiServer=''

def runEyeFi():


    # open file logging
    logfile = args.logfile[0]
    fileHandler = logging.handlers.TimedRotatingFileHandler(logfile, "D", 7, backupCount=7, encoding=None)
    fileHandler.setFormatter(eyeFiLoggingFormat)
    eyeFiLogger.addHandler(fileHandler)

    configfile = args.configure[0]
    eyeFiLogger.info("Reading config " + configfile)

    config = configparser.ConfigParser()
    if not(config.read(configfile)):
        eyeFiLogger.fatal("Could not read config file: "+configfile )
        exit( 1 )

    eyeFiLogger.debug("Loaded configuration: "+ str(config.sections()))

    server_address = (config.get('EyeFiServer','host_name'), config.getint('EyeFiServer','host_port'))

    # Create an instance of an HTTP server. Requests will be handled
    # by the class EyeFiRequestHandler
    eyeFiServer = EyeFiServer(server_address, EyeFiRequestHandler)
    eyeFiServer.config = config
    eyeFiLogger.info("Eye-Fi server started listening on port " + str(server_address[1]))
    eyeFiServer.serve_forever()


class MyDaemon(Daemon):
    def run(self):
        runEyeFi()


def main():
    pid_file = '/tmp/eyefiserver.pid'
    daemon = MyDaemon()
    result = 0
    if 'start' == args.action[0]:
        result = daemon.start()
        if result!=1:
            print( "EyeFiServer started" )
    elif 'stop' == args.action[0]:
        result = daemon.stop()
        if result!=1:
            print( "EyeFiServer stopped" )
    elif 'restart' == args.action[0]:
        result = daemon.restart()
        if result!=1:
            print( "EyeFiServer restarted" )
    elif 'reload' == args.action[0]:
        result = daemon.reload()
    elif 'status' == args.action[0]:
        result = daemon.status()
        if result==1:
            print( "EyeFiServer is not running" )
        else:
            print( "EyeFiServer is running" )
    elif 'instance' == args.action[0]:
        runEyeFi()
    else:
        print( "Unknown command" )
        sys.exit(2)
        sys.exit(result)

if __name__ == "__main__":
    main()
