object profile extends isabelle.CI_Profile
{
  import isabelle._
  import java.io.FileReader
  import scala.sys.process._
  import org.apache.commons.configuration2._

  override def clean = false

  val afp = Path.explode("$AFP_BASE")
  val afp_thys = afp + Path.explode("thys")
  val afp_id = hg_id(afp)

  sealed abstract class Status(val str: String)
  {
    def merge(that: Status): Status = (this, that) match {
      case (Ok, s) => s
      case (Failed, s) => Failed
      case (Skipped, Failed) => Failed
      case (Skipped, s) => Skipped
    }
  }
  object Status
  {
    def merge(statuses: List[Status]): Status =
      statuses.foldLeft(Ok: Status)(_ merge _)

    def from_results(results: Build.Results, session: String): Status =
      if (results.cancelled(session))
        Skipped
      else if (results(session).ok)
        Ok
      else
        Failed
  }

  case object Ok extends Status("ok")
  case object Skipped extends Status("skipped")
  case object Failed extends Status("failed")

  class Metadata(ini: INIConfiguration)
  {

    def entry_of_session(info: Sessions.Info): Option[String] =
      if (info.dir.dir.file == afp_thys.file)
        Some(info.dir.base.implode)
      else
        None

    def group_by_entry(results: Build.Results): Map[Option[String], List[String]] =
      results.sessions.toList.map { name =>
        entry_of_session(results.info(name)) -> name
      }.groupBy(_._1).view.mapValues(_.map(_._2)).toMap

    def status_as_html(status: Map[Option[String], Status]): String =
    {
      val entries_strings = status.collect {
        case (None, Failed) =>
          s"<li>Distribution</li>"
        case (Some(entry), Failed) =>
          s"""<li><a href="https://devel.isa-afp.org/entries/$entry.html">$entry</a></li>"""
      }

      if (entries_strings.isEmpty)
        ""
      else
        entries_strings.mkString("Failed entries: <ul>", "\n", "</ul>")
    }
  }

  val report_file = Path.explode("$ISABELLE_HOME/report.html").file

  def include = List(afp_thys)
  def select = Nil

  def pre_hook(args: List[String]) =
  {
    println(s"AFP id $afp_id")
    if (report_file.exists())
      report_file.delete()

    File.write(report_file, "")
  }

  def post_hook(results: Build.Results) =
  {
    val metadata = {
      val path = afp + Path.explode("metadata/metadata")
      val ini = new INIConfiguration()
      if (path.is_file) {
        val reader = new FileReader(path.file)
        ini.read(reader)
        reader.close()
      }
      new Metadata(ini)
    }

    val status =
      metadata.group_by_entry(results).view.mapValues { sessions =>
        Status.merge(sessions.map(Status.from_results(results, _)))
      }.toMap

    print_section("REPORT")
    println("Writing report file ...")
    File.write(report_file, metadata.status_as_html(status))
    print_section("COMPLETED")
  }

  def selection =
    Sessions.Selection(
      all_sessions = true,
      exclude_session_groups = List("slow"))

}
