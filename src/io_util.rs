use byteorder::ReadBytesExt;
use openssl::ssl::{SslStream, MaybeSslStream};
use std::old_io;
use std::io;
use std::io::prelude::*;
use std::net::TcpStream;
#[cfg(feature = "unix_socket")]
use unix_socket::UnixStream;

use {ConnectParams, SslMode, ConnectTarget, ConnectError};
use message;
use message::WriteMessage;
use message::FrontendMessage::SslRequest;

const DEFAULT_PORT: u16 = 5432;

pub type MainStream = IoShim<MaybeSslStream<IoShim<InternalStream>>>;

pub enum InternalStream {
    Tcp(TcpStream),
    #[cfg(feature = "unix_socket")]
    Unix(UnixStream),
}

impl Read for InternalStream {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match *self {
            InternalStream::Tcp(ref mut s) => s.read(buf),
            #[cfg(feature = "unix_socket")]
            InternalStream::Unix(ref mut s) => s.read(buf),
        }
    }
}

impl Write for InternalStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match *self {
            InternalStream::Tcp(ref mut s) => s.write(buf),
            #[cfg(feature = "unix_socket")]
            InternalStream::Unix(ref mut s) => s.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match *self {
            InternalStream::Tcp(ref mut s) => s.flush(),
            #[cfg(feature = "unix_socket")]
            InternalStream::Unix(ref mut s) => s.flush(),
        }
    }
}

fn open_socket(params: &ConnectParams) -> Result<InternalStream, ConnectError> {
    let port = params.port.unwrap_or(DEFAULT_PORT);
    match params.target {
        ConnectTarget::Tcp(ref host) => {
            Ok(try!(TcpStream::connect(&(&**host, port)).map(InternalStream::Tcp)))
        }
        #[cfg(feature = "unix_socket")]
        ConnectTarget::Unix(ref path) => {
            let path = path.join(&format!(".s.PGSQL.{}", port));
            Ok(try!(UnixStream::connect(&path).map(InternalStream::Unix)))
        }
    }
}

pub fn initialize_stream(params: &ConnectParams, ssl: &SslMode)
                         -> Result<MainStream, ConnectError> {
    let mut socket = try!(open_socket(params));

    let (ssl_required, ctx) = match *ssl {
        SslMode::None => return Ok(IoShim { s: MaybeSslStream::Normal(IoShim { s: socket }) }),
        SslMode::Prefer(ref ctx) => (false, ctx),
        SslMode::Require(ref ctx) => (true, ctx)
    };

    try!(socket.write_message(&SslRequest { code: message::SSL_CODE }));
    try!(socket.flush());

    if try!(socket.read_u8()) == 'N' as u8 {
        if ssl_required {
            return Err(ConnectError::NoSslSupport);
        } else {
            return Ok(IoShim { s: MaybeSslStream::Normal(IoShim { s: socket }) });
        }
    }

    match SslStream::new(ctx, IoShim { s: socket }) {
        Ok(stream) => Ok(IoShim { s: MaybeSslStream::Ssl(stream) }),
        Err(err) => Err(ConnectError::SslError(err))
    }
}

fn translate_error(e: old_io::IoError) -> io::Error {
    use std::old_io::IoErrorKind;
    use std::io::ErrorKind;

    let old_io::IoError { kind, desc, detail } = e;

    let kind = match kind {
        IoErrorKind::FileNotFound => ErrorKind::FileNotFound,
        IoErrorKind::PermissionDenied => ErrorKind::PermissionDenied,
        IoErrorKind::ConnectionRefused => ErrorKind::ConnectionRefused,
        IoErrorKind::ConnectionReset => ErrorKind::ConnectionReset,
        IoErrorKind::ConnectionAborted => ErrorKind::ConnectionAborted,
        IoErrorKind::NotConnected => ErrorKind::NotConnected,
        IoErrorKind::BrokenPipe => ErrorKind::BrokenPipe,
        IoErrorKind::PathAlreadyExists => ErrorKind::PathAlreadyExists,
        IoErrorKind::PathDoesntExist => ErrorKind::PathDoesntExist,
        IoErrorKind::MismatchedFileTypeForOperation => ErrorKind::MismatchedFileTypeForOperation,
        IoErrorKind::ResourceUnavailable => ErrorKind::ResourceUnavailable,
        IoErrorKind::InvalidInput => ErrorKind::InvalidInput,
        IoErrorKind::TimedOut => ErrorKind::TimedOut,
        IoErrorKind::ShortWrite(..) => ErrorKind::WriteZero,
        _ => ErrorKind::Other,
    };

    io::Error::new(kind, desc, detail)
}

fn untranslate_error(e: io::Error) -> old_io::IoError {
    use std::old_io::IoErrorKind;
    use std::io::ErrorKind;

    let kind = match e.kind() {
        ErrorKind::FileNotFound => IoErrorKind::FileNotFound,
        ErrorKind::PermissionDenied => IoErrorKind::PermissionDenied,
        ErrorKind::ConnectionRefused => IoErrorKind::ConnectionRefused,
        ErrorKind::ConnectionReset => IoErrorKind::ConnectionReset,
        ErrorKind::ConnectionAborted => IoErrorKind::ConnectionAborted,
        ErrorKind::NotConnected => IoErrorKind::NotConnected,
        ErrorKind::BrokenPipe => IoErrorKind::BrokenPipe,
        ErrorKind::PathAlreadyExists => IoErrorKind::PathAlreadyExists,
        ErrorKind::PathDoesntExist => IoErrorKind::PathDoesntExist,
        ErrorKind::MismatchedFileTypeForOperation => IoErrorKind::MismatchedFileTypeForOperation,
        ErrorKind::ResourceUnavailable => IoErrorKind::ResourceUnavailable,
        ErrorKind::InvalidInput => IoErrorKind::InvalidInput,
        ErrorKind::TimedOut => IoErrorKind::TimedOut,
        ErrorKind::WriteZero => IoErrorKind::ShortWrite(0),
        _ => IoErrorKind::OtherIoError,
    };

    old_io::IoError {
        kind: kind,
        desc: e.description(),
        detail: e.detail(),
    }
}

struct IoShim<S> {
    s: S
}

impl<S: Reader> Read for IoShim<S> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self.s.read(buf) {
            Ok(n) => Ok(n),
            Err(old_io::IoError { kind: old_io::IoErrorKind::EndOfFile, .. }) => Ok(0),
            Err(e) => Err(translate_error(e))
        }
    }
}

impl<S: Writer> Write for IoShim<S> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self.s.write_all(buf) {
            Ok(()) => Ok(buf.len()),
            Err(e) => Err(translate_error(e))
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        self.s.flush().map_err(translate_error)
    }
}

impl<S: Read> Reader for IoShim<S> {
    fn read(&mut self, buf: &mut [u8]) -> old_io::IoResult<usize> {
        match self.s.read(buf) {
            Ok(0) => Err(old_io::standard_error(old_io::IoErrorKind::EndOfFile)),
            Ok(n) => Ok(n),
            Err(e) => Err(untranslate_error(e)),
        }
    }
}

impl<S: Write> Writer for IoShim<S> {
    fn write_all(&mut self, buf: &[u8]) -> old_io::IoResult<()> {
        self.s.write_all(buf).map_err(untranslate_error)
    }

    fn flush(&mut self) -> old_io::IoResult<()> {
        self.s.flush().map_err(untranslate_error)
    }
}
