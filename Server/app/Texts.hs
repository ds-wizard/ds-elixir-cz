{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Texts where

import Data.Monoid ((<>))
import           Text.RawString.QQ
import           Text.Blaze.Html5 (Html, (!)) 
import qualified Text.Blaze.Html5 as H
import           Text.Blaze.Html5.Attributes as A

vision :: Html
vision = H.preEscapedString [r|
    <table>
      <tbody>
        <tr>
          <td>
            <p>
              <strong>Let's dig the gold mine!</strong>
            </p>
            <p>
              Bioinformatics produces a lot of data that is very valuable and that's our gold mine.
            </p>
            <p>
              In our working group, we realize this value of data. We set ourselves the following goals, by which we want to help BioMed researchers mine their gold:
            </p>
            <ul>
              <li>Collect and provide the information about bioinformatics data produced.</li>
              <li>Help the data producers to take care about their data (a.k.a. Data Stewardship).</li>
              <li>Help the data producers share their data with others.</li>
              <li>Connect and help interested parties to use the available data sources.</li>
            </ul>
            <p>
              Sharing the data sources contents poses challenges regarding technical solutions, organisational set up, security and legal issues. The ultimate goal is making the data <a href='https://www.force11.org/group/fairgroup'>F.A.I.R.</a>, i.e. <em>Findable, Accessible, Interoperable, Re-usable</em> while maintaining all the necessary constraints.
            </p>
            <p>
              Check our <a href="#" onclick="Haste['toAction']()">action steps</a>.
            </p>
          </td>
          <td style="vertical-align: middle; text-align: right;">
            <img src="/static/img/goldmine.jpg" alt="gold mine"><br>
            <a href="http://cliparts.co" style="font-size: 60%; color: gray;">Clip art image by Cliparts.co</a> 
          </td>
        </tr>
      </tbody>
    </table>
|]

actionSteps :: Html
actionSteps = H.preEscapedString [r|
    <table>
      <tbody>
        <tr>
          <td>
            <p>
              Let's start to collect information about the current state of life science (bioinformatic) data. We plan to do this using two simple steps:
            </p>
            <ol>
              <li><strong><a href="#" onclick="Haste['toMQuestionnaire']()">Managerial-level questionnaire</a> (currently open)</strong></li>
              <li><strong><a href="#" onclick="Haste['toTQuestionnaire']()">Technical-level questionnaire</a> (will be based on the results of the previous)</strong></li>
            </ol>
            <p>
              Please help us by diligently answering the questions. Before you start, read the methodical guidelines in the following tabs.
            </p>  
            <ul>
                <li><strong><a href="#" onclick="Haste['toLifecycle']()">Life cycle</a></strong> tab presents a concise conceptual scheme of bioinformatics data.</li>
                <li><strong><a href="#" onclick="Haste['toData']()">Data</a></strong> tab explains data categories and related terms.</li>
                <li><strong><a href="#" onclick="Haste['toRoles']()">Roles</a></strong> tab provides definitions of personal categories.</li>
            </ul>
          </td>
          <td style="vertical-align: middle; text-align: right;">
            <img src="/static/img/goldmine.jpg" alt="gold mine"><br>
            <a href="http://cliparts.co" style="font-size: 60%; color: gray;">Clip art image by Cliparts.co</a> 
          </td>
        </tr>
      </tbody>
    </table>
|]
  
lifeCycle :: Html
lifeCycle = H.preEscapedString [r|
    <table>
      <tbody>
        <tr>
          <td>
            <p>
              The questionnaire is founded on the data lifecycle. Click each stage to learn the details:
            </p>
            <object type='image/svg+xml' id='svg_lifecycle' data='/static/img/data_process.svg' href='http://caniuse.com/#feat=svg'>Your browser does not support SVG</object>
          </td>
          <td style="vertical-align: middle; text-align: right;">
            <img src="/static/img/goldmine.jpg" width="200" style="padding-top: 200px;" alt="gold mine"><br>
            <a href="http://cliparts.co" style="font-size: 60%; color: gray;">Clip art image by Cliparts.co</a> 
          </td>
        </tr>
      </tbody>
    </table>
|]

dataText :: Html
dataText = H.preEscapedString [r|
  <p>
    The data from the lifecycle are summarised here:
  </p>
  <table class='table-text'>
  <tbody>
    <tr>
       <th>Raw data</th>
       <td>Data produced by a technology in stage 1 such as NGS, Arrays, X-Ray, NMR or MassSpec. This data is typically further processed and not used directly.</td>
       <td><object id="svg_raw" width="600" type='image/svg+xml' data='/static/img/data_process.svg' href='http://caniuse.com/#feat=svg'>Your browser does not support SVG</object></td>
    </tr>
    <tr>
       <th>Primary data, Processed data</th>
       <td>Raw data processed in stage 2 by actions such as data splitting, quality control and benchmarking, data filtering, annotating by metadata. Raw data may be acquired either by internal data production or provided by an external subject. Other data and tools may be necessary to process data.</td>
       <td><object id="svg_primary" width="600" type='image/svg+xml' data='/static/img/data_process.svg' href='http://caniuse.com/#feat=svg'>Your browser does not support SVG</object></td>
    </tr>
    <tr>
       <th>Secondary data</th>
       <td>Data that originate in stage 3 from primary data by applying tools and pipelines for e.g. RNA-Seq, Chip-Seq, De-novo sequencing, X-Ray refinement or MS Masquot. Secondary data represent a <em>new level of knowledge</em> by combining data with standardised public data. The input primary data may be acquired either by internal data processing or provided by an external subject.</td>
       <td><object id="svg_secondary" width="600" type='image/svg+xml' data='/static/img/data_process.svg' href='http://caniuse.com/#feat=svg'>Your browser does not support SVG</object></td>
    </tr>
    <tr>
       <th>Standardised public data</th>
       <td>Data publicly available in open-access regime. May be needed for stage 3. A typical examples are the GeneBank, Uniprot or Human Protein Atlas.</td>
       <td><object id="svg_public" width="600" type='image/svg+xml' data='/static/img/data_process.svg' href='http://caniuse.com/#feat=svg'>Your browser does not support SVG</object></td>
    </tr>
  </tbody>
  </table>
|]

roles :: Html
roles = H.preEscapedString [r|
  <p>
    Roles definitions strive to follow the bioinformatics community consensus.
  </p>
  <table class='table-text'>
  <tbody>
    <tr id="consumer_role_desc">
       <th>Data consumer / user</th>
       <td>Also called a data user - a general role, which uses the data for some specific purpose.</td>
       <td><object id="svg_consumer" width="600" type='image/svg+xml' data='/static/img/data_process.svg' href='http://caniuse.com/#feat=svg'>Your browser does not support SVG</object></td>
    </tr>
    <tr id="curator_role_desc">
       <th><a href="https://en.wikipedia.org/wiki/Data_curation" target="_blank">Data curator</a></th>
       <td>Takes care about the data. They are interested in the contents and guarantee data quality.</td>
       <td><object id="svg_curator" width="600" type='image/svg+xml' data='/static/img/data_process.svg' href='http://caniuse.com/#feat=svg'>Your browser does not support SVG</object></td>
    </tr>
    <tr id="custodian_role_desc">
       <th><a href="https://en.wikipedia.org/wiki/Data_custodian" target="_blank">Data custodian</a></th>
       <td>Custodian is a pure technical role. They provide the service of holding the data for you. They are just not interested in the data contents nor form, but the storage architecture.</td>
       <td><object id="svg_custodian" width="600" type='image/svg+xml' data='/static/img/data_process.svg' href='http://caniuse.com/#feat=svg'>Your browser does not support SVG</object></td>
    </tr>
    <tr id="expert_role_desc">
       <th>Data expert</th>
       <td>A technical role (usually an informatician) with the ability to process and/or transform produced data. He physically operates on the data and he is concerned with the form of data. They perform operations like transforming data from XML to database.</td>
       <td><object id="svg_expert" width="600" type='image/svg+xml' data='/static/img/data_process.svg' href='http://caniuse.com/#feat=svg'>Your browser does not support SVG</object></td>
    </tr>
    <tr id="manager_role_desc">
       <th><a href="https://en.wikipedia.org/wiki/Data_management" target="_blank">Data manager</a></th>
       <td>An operative managerial role responsible for managing data acquiring, processing and other data-related affairs by operating other roles.</td>
       <td><object id="svg_manager" width="600" type='image/svg+xml' data='/static/img/data_process.svg' href='http://caniuse.com/#feat=svg'>Your browser does not support SVG</object></td>
    </tr>
    <tr id="producer_role_desc">
       <th>Data producer</th>
       <td>A technical role responsible for producing data by operating specific technical devices.</td>
       <td><object id="svg_producer" width="600" type='image/svg+xml' data='/static/img/data_process.svg' href='http://caniuse.com/#feat=svg'>Your browser does not support SVG</object></td>
    </tr>
    <tr id="steward_role_desc">
       <th><a href="https://en.wikipedia.org/wiki/Data_steward" target="_blank">Data steward</a></th>
       <td>The highest managerial role who is responsible for all tasks of data stewardship, i.e. Planning, Data Management and Sustainability. He operates other roles to carry these out.</td>
       <td><object id="svg_steward" width="600" type='image/svg+xml' data='/static/img/data_process.svg' href='http://caniuse.com/#feat=svg'>Your browser does not support SVG</object></td>
    </tr>
    <tr id="investigator_role_desc">
       <th><a href="https://en.wikipedia.org/wiki/Principal_investigator" target="_blank">Principal investigator</a></th>
       <td>Is the official accountable head of a project. He instructs other roles to perform various tasks.</td>
       <td><object id="svg_investigator" width="600" type='image/svg+xml' data='/static/img/data_process.svg' href='http://caniuse.com/#feat=svg'>A browser with SVG support needed.</object></td>
    </tr>
  </tbody>
  </table>
  <p>
    It is important to understand that roles are abstracted from the executing people:
  </p>
  <ul>
    <li>Several roles may be assigned to one person.</li>
    <li>One role may be carried out by several people.</li>
  </ul>
|]
overlay1 :: Html
overlay1 = do 
  H.h3 "1. Data Production"
  H.p "The first step in acquiring data is its primary production. The produced data usually come from measurement devices such as NGS, Arrays, X-Ray, NMR or MassSpec. In this step, we do not apply any further processing."
  H.table ! A.class_ "table-text" $ do
    H.tbody $ do
      H.tr $ do
        H.th "Prerequisites for the stage:"
        H.td "Technical devices for producing the data"
      H.tr $ do
        H.th "Result of the stage:"
        H.td "Raw data acquired from a measurement device"
      H.tr $ do
        H.th "Involved roles:"
        H.td $ do
          _ <- "Data producer"
          H.br
          _ <- "Data manager"
          H.br
          "Data steward"


overlay2 :: Html
overlay2 = do 
  H.h3 "2. Data Processing"
  H.p ("Data produced in the first step are subsequently processed to " <> H.strong "prepare data for research" <> ". Processing means applying transformations on data such as data splitting, quality control and benchmarking, data filtering, annotating by metadata. data_processing is usually not the ultimate goal, it is done to prepare data for using in the next step. In rare situations, the processing may not be necessary for using the data, e.g. in collaboration projects.")
  H.p "Data processing may consist of several steps from the raw data to the first interoperable standard format of the data, which is suitable for general use, i.e. temporary internal formats are not considered."
  H.table ! A.class_ "table-text" $ do
    H.tbody $ do
      H.tr $ do
        H.th "Prerequisites for the stage:"
        H.td "Raw data"
      H.tr $ do
        H.th "Result of the stage:"
        H.td "Processed data; also called Primary data"
      H.tr $ do
        H.th "Involved roles:"
        H.td $ do
          _ <- "Data expert"
          H.br
          _ <- "Data curator"
          H.br
          _ <- "Data manager"
          H.br
          "Data steward"

overlay3 :: Html
overlay3 = do 
  H.h3 "3. Data Usage"
  H.p ("In this step, the processed (ev. raw) data are used for their purpose like RNA-Seq, Chip-Seq, De-novo sequencing, X-Ray refinement or MS Masquot. Also, new data may be produced as a result of the analysis and usage. Such data differ from the data produced in stage 2, as they " <> H.strong "form a new level of knowledge" <> " (while the data processing results in stage 2 produce data on the same level of knowledge). This is distinguished by calling the data produced in this stage as \"Secondary data\".")
  H.table ! A.class_ "table-text" $ do
    H.tbody $ do
      H.tr $ do
        H.th "Prerequisites for the stage:"
        H.td "Processed data, ev. raw data (not recommended). Standardised public data may be needed."
      H.tr $ do
        H.th "Result of the stage:"
        H.td "Data are used (consumed) for their purpose and possibly new data are produced, which are called Secondary data."
      H.tr $ do
        H.th "Involved roles:"
        H.td $ do
          _ <- "Data consumer"
          H.br
          _ <- "Data curator"
          H.br
          _ <- "Data expert"
          H.br
          "Data steward"

overlay4 :: Html
overlay4 = do 
  H.h3 "4. Data Storage"
  H.p "Data are naturally stored in some form in each of the previous stages, usually as files on a hard drive. However, we are not interested in temporary auxiliary data storing before processing them. On the contrary, storing raw data in a more permanent way is generally not a good practice, data should be processed before storing them. Apart from mere saving files to disk, this may encompass a.o.:"
  H.ul $ do
    H.li "Storing data in a specific format to make it interchangeable"
    H.li "Ensuring persistence (backup) and security"
    H.li "Storing data description (metadata) together with the data"
    H.li "Cataloguing the data file and making it findable"
  H.p "This activity is solely focused on internal data storage. Making the data accessible is the concern of the \"Data Availability\" stage."
  H.table ! A.class_ "table-text" $ do
    H.tbody $ do
      H.tr $ do
        H.th "Prerequisites for the stage:"
        H.td "Primary data, ev. raw data"
      H.tr $ do
        H.th "Result of the stage:"
        H.td "Data are stored"
      H.tr $ do 
        H.th "Involved roles:"
        H.td $ do
          _ <- "Data curator"
          H.br
          _ <- "Data custodian"
          H.br
          _ <- "Data expert"
          H.br
          _ <- "Data manager"
          H.br
          "Data steward"

overlay5 :: Html
overlay5 = do 
  H.h3 "5. Data Accessibility"
  H.p "Data are made available for the external users in this stage. The data may come from all the stages -- from raw data to the secondary data. Data availability means providing data in a suitable format via a technical solution. This may be:"
  H.ul $ do
    H.li "Data file available for download via http, ftp and similar protocols"
    H.li "Data server available for connecting for client applications, such as #TODO"
    H.li "Offering data through a web (REST) service"
    H.li $ do 
      _ <- "Offering data through a web application (e.g. "
      H.a ! A.href "http://www.proteinatlas.org/" $ "http://www.proteinatlas.org/"
      ")"
  H.table ! A.class_ "table-text" $ do
    H.tbody $ do
      H.tr $ do
        H.th "Prerequisites for the stage:"
        H.td "Stored data"
      H.tr $ do
        H.th "Result of the stage:"
        H.td "Data are made externally available"
      H.tr $ do
        H.th "Involved roles:"
        H.td $ do
          _ <- "Data curator"
          H.br
          _ <- "Data custodian"
          H.br
          _ <- "Data manager"
          H.br
          "Data steward"

overlay6 :: Html
overlay6 = do 
  H.h3 "6. Data management"
  H.p $  H.preEscapedString "Data management is the process focused on the long-term maintainability of data. It strives that the data are <a href=\"https://www.force11.org/group/fairgroup\">F.A.I.R.</a>, i.e. Findable, Accessible, Interoperable, Reusable. Data stewardship encompasses a.o.:"
  H.ul $ do
    H.li "Making data actual (updates of data)"
    H.li "Making data correct (handling of errors in data)"
    H.li "Data change management -- data versioning"
  H.p "We typically speak about data stewardship with the respect to data availability, however, the stewardship may be just internal, as depicted byt the two distinct arrows in the figure."
  H.table ! A.class_ "table-text" $ do
    H.tbody $ do
      H.tr $ do
        H.th "Prerequisites for the stage:"
        H.td "Stored data, possibly already made available"
      H.tr $ do
        H.th "Result of the stage:"
        H.td $ H.preEscapedString "Data are maintained in a long-term horizon, they exhibit <a href=\"https://www.force11.org/group/fairgroup\">F.A.I.R.</a> qualities. Data stewardship is the focus of the data interoperability initiative"
      H.tr $ do
        H.th "Involved roles:"
        H.td $ do
          _ <- "Data curator"
          H.br
          _ <- "Data manager"
          H.br
          "Data steward"
