import unittest
import pymysql
from unittest.mock import patch, MagicMock
from src.server.DatabaseManager import DatabaseManager
from flask import Flask

class TestDatabaseManager(unittest.TestCase):
    
    def setUp(self):
        self.app = Flask(__name__)
        self.app.config['MYSQL_HOST'] = 'localhost'
        self.app.config['MYSQL_USER'] = 'user'
        self.app.config['MYSQL_PASSWORD'] = 'password'
        self.app.config['MYSQL_DB'] = 'test_db'
        self.app.config['MYSQL_PORT'] = 3306
        self.db_manager = DatabaseManager(self.app)

    @patch('pymysql.connect')
    def test_connect(self, mock_connect):
        """Test that the connect method establishes a database connection."""
        self.db_manager.connect()
        mock_connect.assert_called_once_with(
            host='localhost',
            user='user',
            password='password',
            database='test_db',
            port=3306
        )
        self.assertIsNotNone(self.db_manager.connection)

    @patch('pymysql.connect')
    def test_close(self, mock_connect):
        """Test that the close method closes the database connection if it exists."""
        mock_connection = MagicMock()
        self.db_manager.connection = mock_connection
        self.db_manager.close()
        mock_connection.close.assert_called_once()
        self.assertIsNone(self.db_manager.connection)

    @patch('pymysql.connect')
    def test_execute_query(self, mock_connect):
        """Test execute_query runs a query and fetches results."""
        mock_connection = MagicMock()
        mock_cursor = MagicMock()
        mock_cursor.fetchall.return_value = [("result1",), ("result2",)]
        mock_connection.cursor.return_value = mock_cursor
        mock_connect.return_value = mock_connection
        result = self.db_manager.execute_query("SELECT * FROM test_table")
        mock_cursor.execute.assert_called_once_with("SELECT * FROM test_table", ())
        mock_cursor.fetchall.assert_called_once()
        self.assertEqual(result, [("result1",), ("result2",)])

    @patch('pymysql.connect')
    def test_execute_commit(self, mock_connect):
        """Test execute_commit runs a query and commits the transaction."""
        mock_connection = MagicMock()
        mock_cursor = MagicMock()       
        mock_connection.cursor.return_value = mock_cursor
        mock_connect.return_value = mock_connection
        self.db_manager.execute_commit("INSERT INTO test_table (col) VALUES (%s)", ("value",))
        mock_cursor.execute.assert_called_once_with("INSERT INTO test_table (col) VALUES (%s)", ("value",))
        mock_connection.commit.assert_called_once()

    @patch('pymysql.connect')
    def test_connection_error(self, mock_connect):
        """Test connection error handling when database credentials are incorrect."""
        mock_connect.side_effect = pymysql.MySQLError("Connection failed")
        with self.assertRaises(pymysql.MySQLError):
            self.db_manager.connect()

    @patch('pymysql.connect')
    def test_query_error_handling(self, mock_connect):
        """Test error handling when executing an invalid SQL query."""
        mock_connection = MagicMock()
        mock_cursor = MagicMock()
        mock_cursor.execute.side_effect = pymysql.MySQLError("Syntax error")
        mock_connection.cursor.return_value = mock_cursor
        mock_connect.return_value = mock_connection
        with self.assertRaises(pymysql.MySQLError):
            self.db_manager.execute_query("INVALID SQL QUERY")
        mock_connection.close.assert_called_once()


if __name__ == "__main__":
    unittest.main()
